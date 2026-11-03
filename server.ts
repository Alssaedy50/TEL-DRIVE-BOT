import express from 'express';
import path from 'path';
import fs from 'fs';
import https from 'https';
import { createDecipheriv } from 'crypto';
import { execFile } from 'child_process';
import { promisify } from 'util';
import dotenv from 'dotenv';
import { TelegramClient, Api, utils, errors } from 'telegram';
import { StringSession } from 'telegram/sessions/index.js';
import { CustomFile } from 'telegram/client/uploads.js';
import bigInt from 'big-integer';

const execFileAsync = promisify(execFile);

dotenv.config();

export const app = express();
const PORT = Number(process.env.PORT) || 3000;
const IS_VERCEL = Boolean(process.env.VERCEL || process.env.VERCEL_ENV);
let lastDetectedOrigin = '';
let isWebhookRegistered = false;
let activeWebhookUrl: string | null = null;

app.use(express.json({ limit: '50mb' }));
app.use((req, res, next) => {
  // Normalize req.url when rewritten by Vercel serverless /api/index
  const matchedPath =
    (req.headers['x-matched-path'] as string) ||
    (req.headers['x-forwarded-uri'] as string);
  if (matchedPath && matchedPath.startsWith('/api') && req.url !== matchedPath) {
    req.url = matchedPath;
  }
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  if (req.method === 'OPTIONS') {
    res.status(204).end();
    return;
  }
  next();
});

// ============================================================================
// Types & State
// ============================================================================

export interface BotInfo {
  id: number;
  is_bot: boolean;
  first_name: string;
  username: string;
}

export type CompressMode = 'none' | 'zip' | 'media';

export interface TransferJob {
  id: string;
  source: 'telegram' | 'url' | 'web' | 'drive_to_telegram' | 'url_to_telegram';
  direction?: 'to_drive' | 'to_telegram' | 'to_device';
  protocol?: 'bot_api' | 'mtproto' | 'http';
  mediaFormat?: 'video' | 'audio';
  quality?: string;
  compressMode?: CompressMode;
  fileName: string;
  mimeType: string;
  totalBytes: number;
  bytesTransferred: number;
  speedBps: number;
  status: 'queued' | 'waiting_auth' | 'downloading' | 'uploading' | 'completed' | 'failed' | 'cancelled';
  isDuplicateSkipped?: boolean;
  errorMessage?: string;
  senderName: string;
  senderUsername?: string;
  accountEmail?: string;
  chatId?: number;
  messageId?: number;
  statusMessageId?: number;
  telegramFileId?: string;
  telegramFileUniqueId?: string;
  directUrl?: string;
  driveFileId?: string;
  webViewLink?: string;
  folderId?: string;
  folderName?: string;
  resumableSessionUri?: string;
  resumableUploadedOffset?: number;
  createdAt: string;
  completedAt?: string;
}

export interface KnownTelegramUser {
  chatId: number;
  name: string;
  username?: string;
  linkedEmail?: string | null;
  lastSeenAt: string;
  transfersCount: number;
  blocked: boolean;
}

export interface UserDriveProfile {
  profileId: string;
  accessToken: string | null;
  userEmail: string | null;
  userName: string | null;
  chatId: number | null;
  telegramName?: string | null;
  telegramUsername?: string | null;
  linkCode: string;
  activeFolderId: string | null;
  activeFolderName: string;
  accountEnabled: boolean;
  autoCategorizeByType: boolean;
  skipDuplicates: boolean;
  urlHandlingMode: 'ask' | 'to_drive' | 'to_telegram';
  defaultQuality: string;
  defaultCompressMode: CompressMode;
  lastSyncedAt: string | null;
}

export interface AdminConfigState {
  ownerChatId: number | null;
  ownerName: string | null;
  ownerUsername: string | null;
  accessMode: 'public' | 'owner_only';
  botPaused: boolean;
  accountEnabled: boolean;
  urlHandlingMode: 'ask' | 'to_drive' | 'to_telegram';
  defaultQuality: string;
  defaultCompressMode: CompressMode;
  knownUsers: Record<string, KnownTelegramUser>;
}

interface DriveSessionState {
  accessToken: string | null;
  userEmail: string | null;
  userName: string | null;
  activeFolderId: string | null;
  activeFolderName: string;
  lastSyncedAt: string | null;
}

const STATE_CACHE_PATH = '/tmp/telegram_drive_bot_state.json';
const MTPROTO_SESSION_PATH = '/tmp/telegram_mtproto_bot_session.txt';
const MTPROTO_POOL_CACHE_PATH = '/tmp/telegram_mtproto_pool_sessions.json';
const MTPROTO_POOL_SIZE = 6;

const DEFAULT_TELEGRAM_API_ID = 2040;
const DEFAULT_TELEGRAM_API_HASH = 'b18441a1ff607e10a989891a5462e627';

const driveSession: DriveSessionState = {
  accessToken: null,
  userEmail: null,
  userName: null,
  activeFolderId: null,
  activeFolderName: 'Telegram Bot Uploads',
  lastSyncedAt: null,
};

const adminConfig: AdminConfigState = {
  ownerChatId: null,
  ownerName: null,
  ownerUsername: null,
  accessMode: 'public',
  botPaused: false,
  accountEnabled: true,
  urlHandlingMode: 'ask',
  defaultQuality: '720',
  defaultCompressMode: 'none',
  knownUsers: {},
};

// Multi-user Personal Profiles Map (keyed by lowercase email or chat_<chatId>)
const userProfiles: Record<string, UserDriveProfile> = {};

function generateLinkCode(): string {
  return Math.random().toString(36).substring(2, 8).toUpperCase();
}

let botInfo: BotInfo | null = null;
let botConnectionError: string | null = null;
let isPolling = false;
let lastUpdateId = 0;
let pollingAbortController: AbortController | null = null;
let autoCategorizeByType = false;
let skipDuplicates = true;

// Active AbortControllers per job for instant upload cancellation
const jobAbortControllers = new Map<string, AbortController>();

// Interactive conversation state sets
const awaitingFolderNameChats = new Set<number>();
const awaitingUrlToTelegramChats = new Set<number>();
const awaitingDriveSearchChats = new Set<number>();
const cachedFoldersById = new Map<string, string>();
const pendingUrlChoices = new Map<
  string,
  {
    url: string;
    chatId: number;
    messageId: number;
    senderName: string;
    senderUsername?: string;
    selectedQuality: string;
    compressMode: CompressMode;
  }
>();

// MTProto Client State & Multi-Session Worker Pool (for >20MB up to 2GB Telegram files)
let mtprotoClient: TelegramClient | null = null;
const mtprotoPoolClients: TelegramClient[] = [];
let mtprotoConnected = false;
let mtprotoError: string | null = null;

const transferJobs: TransferJob[] = [];

// Restore persisted state from /tmp if available
try {
  if (fs.existsSync(STATE_CACHE_PATH)) {
    const saved = JSON.parse(fs.readFileSync(STATE_CACHE_PATH, 'utf-8'));
    if (saved.driveSession) {
      Object.assign(driveSession, saved.driveSession);
    }
    if (saved.adminConfig) {
      Object.assign(adminConfig, saved.adminConfig);
      if (!adminConfig.defaultQuality) adminConfig.defaultQuality = '720';
      if (!adminConfig.defaultCompressMode) adminConfig.defaultCompressMode = 'none';
    }
    if (typeof saved.autoCategorizeByType === 'boolean') {
      autoCategorizeByType = saved.autoCategorizeByType;
    }
    if (typeof saved.skipDuplicates === 'boolean') {
      skipDuplicates = saved.skipDuplicates;
    }
    if (saved.userProfiles && typeof saved.userProfiles === 'object') {
      Object.assign(userProfiles, saved.userProfiles);
    }
    if (Array.isArray(saved.transferJobs)) {
      transferJobs.push(...saved.transferJobs.slice(0, 150));
    }
  }
} catch {
  // Ignore cache load errors
}

// Seed owner/legacy driveSession into userProfiles for seamless migration
if (driveSession.userEmail) {
  const normEmail = driveSession.userEmail.trim().toLowerCase();
  if (!userProfiles[normEmail]) {
    userProfiles[normEmail] = {
      profileId: normEmail,
      accessToken: driveSession.accessToken,
      userEmail: driveSession.userEmail,
      userName: driveSession.userName,
      chatId: adminConfig.ownerChatId,
      telegramName: adminConfig.ownerName,
      telegramUsername: adminConfig.ownerUsername,
      linkCode: generateLinkCode(),
      activeFolderId: driveSession.activeFolderId,
      activeFolderName: driveSession.activeFolderName || 'Telegram Bot Uploads',
      accountEnabled: adminConfig.accountEnabled,
      autoCategorizeByType,
      skipDuplicates,
      urlHandlingMode: adminConfig.urlHandlingMode || 'ask',
      defaultQuality: adminConfig.defaultQuality || '720',
      defaultCompressMode: adminConfig.defaultCompressMode || 'none',
      lastSyncedAt: driveSession.lastSyncedAt,
    };
  }
}

function getOrCreateUserProfile(opts: {
  email?: string | null;
  chatId?: number | null;
  createIfMissing?: boolean;
}): UserDriveProfile {
  const cleanEmail = opts.email ? opts.email.trim().toLowerCase() : '';
  const chatId = opts.chatId && !isNaN(Number(opts.chatId)) ? Number(opts.chatId) : null;

  // 1. Lookup by email
  if (cleanEmail && userProfiles[cleanEmail]) {
    const prof = userProfiles[cleanEmail];
    if (chatId && !prof.chatId) {
      prof.chatId = chatId;
    }
    return prof;
  }

  // 2. Lookup by chatId across all profiles
  if (chatId) {
    const byChat = Object.values(userProfiles).find((p) => p.chatId === chatId);
    if (byChat) {
      if (cleanEmail && !byChat.userEmail) {
        // Migrate chat_<id> profile to email key
        delete userProfiles[byChat.profileId];
        byChat.profileId = cleanEmail;
        byChat.userEmail = opts.email!.trim();
        userProfiles[cleanEmail] = byChat;
      }
      return byChat;
    }

    // If ownerChatId matches legacy driveSession
    if (chatId === adminConfig.ownerChatId && driveSession.userEmail) {
      const ownerKey = driveSession.userEmail.trim().toLowerCase();
      if (userProfiles[ownerKey]) {
        userProfiles[ownerKey].chatId = chatId;
        return userProfiles[ownerKey];
      }
    }
  }

  const key = cleanEmail || (chatId ? `chat_${chatId}` : 'default');
  if (userProfiles[key]) {
    return userProfiles[key];
  }

  const newProfile: UserDriveProfile = {
    profileId: key,
    accessToken: null,
    userEmail: opts.email ? opts.email.trim() : null,
    userName: null,
    chatId: chatId || null,
    linkCode: generateLinkCode(),
    activeFolderId: null,
    activeFolderName: 'Telegram Bot Uploads',
    accountEnabled: true,
    autoCategorizeByType: false,
    skipDuplicates: true,
    urlHandlingMode: 'ask',
    defaultQuality: '720',
    defaultCompressMode: 'none',
    lastSyncedAt: null,
  };
  if (opts.createIfMissing !== false) {
    userProfiles[key] = newProfile;
  }
  return newProfile;
}

function findProfileByLinkCode(code: string): UserDriveProfile | null {
  const clean = code.trim().toUpperCase();
  if (!clean) return null;
  return Object.values(userProfiles).find((p) => p.linkCode.toUpperCase() === clean) || null;
}

function getJobsForUser(
  profileOrChatId: UserDriveProfile | number | null | undefined,
  viewAllOrEmail: boolean | string | null | undefined = false
): TransferJob[] {
  if (viewAllOrEmail === true) return transferJobs;

  let profile: UserDriveProfile | null = null;
  if (typeof profileOrChatId === 'number') {
    const emailArg = typeof viewAllOrEmail === 'string' ? viewAllOrEmail : undefined;
    profile = getOrCreateUserProfile({ chatId: profileOrChatId, email: emailArg, createIfMissing: false });
  } else if (profileOrChatId && typeof profileOrChatId === 'object') {
    profile = profileOrChatId;
  } else if (typeof viewAllOrEmail === 'string' && viewAllOrEmail.trim()) {
    profile = getOrCreateUserProfile({ email: viewAllOrEmail.trim(), createIfMissing: false });
  }

  if (!profile) return [];
  const normEmail = profile.userEmail ? profile.userEmail.trim().toLowerCase() : null;
  const chatId = profile.chatId;
  const isOwner =
    (chatId && chatId === adminConfig.ownerChatId) ||
    (normEmail && driveSession.userEmail && normEmail === driveSession.userEmail.trim().toLowerCase());

  return transferJobs.filter((j) => {
    if (normEmail && j.accountEmail && j.accountEmail.trim().toLowerCase() === normEmail) return true;
    if (chatId && j.chatId === chatId) return true;
    if (isOwner && (!j.accountEmail || j.accountEmail === 'default')) return true;
    return false;
  });
}

function saveStateToDisk() {
  try {
    fs.writeFileSync(
      STATE_CACHE_PATH,
      JSON.stringify({
        driveSession,
        adminConfig,
        autoCategorizeByType,
        skipDuplicates,
        userProfiles,
        transferJobs: transferJobs.slice(0, 150),
      }),
      'utf-8'
    );
  } catch {
    // Ignore disk write errors
  }
}

function getBotToken(): string {
  return (process.env.TELEGRAM_BOT_TOKEN || '').trim();
}

function getApiId(): number {
  const raw = (process.env.TELEGRAM_API_ID || '').trim();
  const parsed = parseInt(raw, 10);
  return !isNaN(parsed) && parsed > 0 ? parsed : DEFAULT_TELEGRAM_API_ID;
}

function getApiHash(): string {
  const raw = (process.env.TELEGRAM_API_HASH || '').trim();
  return raw || DEFAULT_TELEGRAM_API_HASH;
}

function getTelegramApiRoot(): string {
  const custom = (process.env.TELEGRAM_API_ROOT || '').trim();
  return custom ? custom.replace(/\/+$/, '') : 'https://api.telegram.org';
}

function getAppUrl(chatId?: number | null): string {
  const envUrl = (process.env.APP_URL || '').trim().replace(/\/+$/, '');
  const vercelProdUrl = (process.env.VERCEL_PROJECT_PRODUCTION_URL || '').trim().replace(/^https?:\/\//, '').replace(/\/+$/, '');
  const vercelBranchUrl = (process.env.VERCEL_URL || '').trim().replace(/^https?:\/\//, '').replace(/\/+$/, '');

  const base =
    envUrl ||
    (vercelProdUrl ? `https://${vercelProdUrl}` : '') ||
    (vercelBranchUrl ? `https://${vercelBranchUrl}` : '') ||
    lastDetectedOrigin;

  if (!base) return '';
  if (chatId) {
    return `${base}?chatId=${encodeURIComponent(String(chatId))}`;
  }
  return base;
}

function formatBytes(bytes: number): string {
  if (!bytes || bytes <= 0) return '0 B';
  const k = 1024;
  const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return `${parseFloat((bytes / Math.pow(k, i)).toFixed(2))} ${sizes[i]}`;
}

function formatCompressModeAr(mode?: CompressMode): string {
  if (mode === 'zip') return 'أرشيف ZIP (.zip)';
  if (mode === 'media') return 'تقليص حجم الميديا (FFmpeg)';
  return 'بدون ضغط (الحجم الأصلي)';
}

// ============================================================================
// MTProto Engine (Supports Telegram files >20MB up to 2GB automatically)
// ============================================================================

const dcExportMutexes = new Map<number, Promise<any>>();

function preventExportedSenderAutoDisconnect(client: TelegramClient, dcId?: number) {
  const timeoutsMap: Map<number, any> | undefined = (client as any)._exportedSenderReleaseTimeouts;
  if (!timeoutsMap) return;
  if (typeof dcId === 'number') {
    if (timeoutsMap.get(dcId)) {
      clearTimeout(timeoutsMap.get(dcId));
      timeoutsMap.delete(dcId);
    }
  } else {
    for (const [k, t] of timeoutsMap.entries()) {
      clearTimeout(t);
      timeoutsMap.delete(k);
    }
  }
}

async function getSafeClientSender(client: TelegramClient, dcId: number): Promise<any> {
  // Fast path: if this client already has an active, connected sender for dcId, return immediately (0ms)
  const existingPromises: Map<number, Promise<any>> | undefined = (client as any)._exportedSenderPromises;
  if (dcId === client.session.dcId && (client as any)._sender?.isConnected?.()) {
    return (client as any)._sender;
  }
  if (existingPromises && existingPromises.has(dcId)) {
    try {
      const existing = await existingPromises.get(dcId);
      if (existing && existing.isConnected && existing.isConnected()) {
        preventExportedSenderAutoDisconnect(client, dcId);
        return existing;
      }
    } catch {
      // Fall through to serialized connect/export
    }
  }

  // Slow path: serialize initial ExportAuthorization per DC so two clients never collide with AUTH_BYTES_INVALID
  const prevMutex = dcExportMutexes.get(dcId) || Promise.resolve();
  const runConnect = async () => {
    const s = await client.getSender(dcId);
    preventExportedSenderAutoDisconnect(client, dcId);
    return s;
  };
  const nextPromise = prevMutex.then(runConnect, runConnect);
  dcExportMutexes.set(
    dcId,
    nextPromise.catch(() => {})
  );
  return nextPromise;
}

// Keep warm DC senders alive every 25s so GramJS's 60s timer never disconnects them
const gramJsKeepAlive = setInterval(() => {
  for (const c of mtprotoPoolClients) {
    preventExportedSenderAutoDisconnect(c);
  }
}, 25000);
if (typeof gramJsKeepAlive.unref === 'function') {
  gramJsKeepAlive.unref();
}

async function createAndConnectSingleMtprotoClient(
  savedSession: string,
  token: string,
  apiId: number,
  apiHash: string
): Promise<{ client: TelegramClient; sessionStr: string }> {
  const client = new TelegramClient(new StringSession(savedSession), apiId, apiHash, {
    connectionRetries: 5,
    autoReconnect: true,
  });
  (client as any).setLogLevel?.('none');

  if (savedSession) {
    await client.connect();
    return { client, sessionStr: savedSession };
  }

  await client.start({
    botAuthToken: token,
  });
  const newSessionStr = String((client.session.save() as unknown as string) || '');
  return { client, sessionStr: newSessionStr };
}

async function startMtprotoEngine(): Promise<void> {
  const token = getBotToken();
  const apiId = getApiId();
  const apiHash = getApiHash();

  if (!token) {
    mtprotoConnected = false;
    return;
  }

  try {
    // Disconnect any previous pool clients cleanly
    for (const oldClient of mtprotoPoolClients.splice(0, mtprotoPoolClients.length)) {
      try {
        await oldClient.disconnect();
      } catch {
        // Ignore disconnect error
      }
    }
    if (mtprotoClient) {
      try {
        await mtprotoClient.disconnect();
      } catch {
        // Ignore disconnect error
      }
      mtprotoClient = null;
      mtprotoConnected = false;
    }

    let savedPoolSessions: string[] = [];
    try {
      if (fs.existsSync(MTPROTO_POOL_CACHE_PATH)) {
        const parsed = JSON.parse(fs.readFileSync(MTPROTO_POOL_CACHE_PATH, 'utf-8'));
        if (Array.isArray(parsed)) {
          savedPoolSessions = parsed.filter((s) => typeof s === 'string' && s.trim().length > 0);
        }
      }
    } catch {
      savedPoolSessions = [];
    }

    if (savedPoolSessions.length === 0 && fs.existsSync(MTPROTO_SESSION_PATH)) {
      try {
        const single = fs.readFileSync(MTPROTO_SESSION_PATH, 'utf-8').trim();
        if (single) savedPoolSessions.push(single);
      } catch {
        // Ignore
      }
    }

    // 1. Connect all already-cached sessions in parallel (< 0.1s)
    if (savedPoolSessions.length > 0) {
      const connectedResults = await Promise.all(
        savedPoolSessions.slice(0, MTPROTO_POOL_SIZE).map(async (sess) => {
          try {
            return await createAndConnectSingleMtprotoClient(sess, token, apiId, apiHash);
          } catch {
            return await createAndConnectSingleMtprotoClient('', token, apiId, apiHash);
          }
        })
      );

      for (const item of connectedResults) {
        mtprotoPoolClients.push(item.client);
      }
      savedPoolSessions = connectedResults.map((r) => r.sessionStr);
    } else {
      // Connect primary client first so bot is ready immediately
      const primary = await createAndConnectSingleMtprotoClient('', token, apiId, apiHash);
      mtprotoPoolClients.push(primary.client);
      savedPoolSessions = [primary.sessionStr];
    }

    mtprotoClient = mtprotoPoolClients[0];
    mtprotoConnected = true;
    mtprotoError = null;

    if (savedPoolSessions[0]) {
      try {
        fs.writeFileSync(MTPROTO_SESSION_PATH, savedPoolSessions[0], 'utf-8');
        fs.writeFileSync(MTPROTO_POOL_CACHE_PATH, JSON.stringify(savedPoolSessions), 'utf-8');
      } catch {
        // Ignore
      }
    }

    console.log(
      `Telegram MTProto 2GB Engine connected (${mtprotoPoolClients.length}/${MTPROTO_POOL_SIZE} parallel sessions ready)!`
    );

    // 2. In background: fill any remaining pool slots up to MTPROTO_POOL_SIZE and pre-warm DC 2 & DC 4
    (async () => {
      try {
        while (mtprotoPoolClients.length < MTPROTO_POOL_SIZE) {
          const extra = await createAndConnectSingleMtprotoClient('', token, apiId, apiHash);
          mtprotoPoolClients.push(extra.client);
          savedPoolSessions.push(extra.sessionStr);
          try {
            fs.writeFileSync(MTPROTO_POOL_CACHE_PATH, JSON.stringify(savedPoolSessions), 'utf-8');
          } catch {
            // Ignore
          }
        }

        // Pre-warm DC 2 and DC 4 senders sequentially via getSafeClientSender so large file downloads start at 0.00s
        for (const dcToWarm of [4, 2]) {
          for (const c of mtprotoPoolClients) {
            try {
              await getSafeClientSender(c, dcToWarm);
            } catch {
              // Ignore pre-warm warnings
            }
          }
        }

        // Auto-resume any interrupted transfers that were active before a server restart
        if (driveSession.accessToken && adminConfig.accountEnabled) {
          for (const j of transferJobs) {
            if (
              (j.status === 'uploading' || j.status === 'downloading' || j.status === 'queued') &&
              !jobAbortControllers.has(j.id)
            ) {
              if (j.direction === 'to_telegram' || j.source === 'drive_to_telegram' || j.source === 'url_to_telegram') {
                executePullToTelegramJob(j);
              } else {
                executeTransferJob(j);
              }
            }
          }
        }
      } catch {
        // Ignore background pool expansion warnings
      }
    })();
  } catch (err: any) {
    mtprotoConnected = false;
    mtprotoError = err?.message || 'تعذر تشغيل محرك MTProto.';
    console.warn('MTProto initialization warning:', mtprotoError);
  }
}

async function getMtprotoMessageForJob(job: TransferJob): Promise<any | null> {
  if (!mtprotoClient || !mtprotoConnected || !job.messageId) return null;

  try {
    if (!mtprotoClient.connected) {
      await mtprotoClient.connect();
    }
    const res: any = await mtprotoClient.invoke(
      new Api.messages.GetMessages({
        id: [new Api.InputMessageID({ id: job.messageId })],
      })
    );
    if (res && Array.isArray(res.messages) && res.messages.length > 0 && res.messages[0]?.media) {
      return res.messages[0];
    }
  } catch (err) {
    console.warn('MTProto GetMessages error:', err);
  }

  return null;
}

// ============================================================================
// Telegram Helper Functions & Inline Keyboards
// ============================================================================

async function telegramApi<T = any>(method: string, body?: Record<string, any>, signal?: AbortSignal): Promise<T> {
  const token = getBotToken();
  if (!token) {
    throw new Error('TELEGRAM_BOT_TOKEN غير مضاف في قسم الأسرار (Secrets).');
  }
  const url = `${getTelegramApiRoot()}/bot${token}/${method}`;
  const res = await fetch(url, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: body ? JSON.stringify(body) : undefined,
    signal,
  });
  const data = await res.json();
  if (!data.ok) {
    throw new Error(data.description || `Telegram API error on ${method}`);
  }
  return data.result as T;
}

async function sendTelegramMessage(
  chatId: number,
  text: string,
  replyToMessageId?: number,
  replyMarkup?: any
): Promise<number | undefined> {
  try {
    const msg = await telegramApi<{ message_id: number }>('sendMessage', {
      chat_id: chatId,
      text,
      parse_mode: 'HTML',
      reply_to_message_id: replyToMessageId,
      disable_web_page_preview: true,
      reply_markup: replyMarkup,
    });
    return msg.message_id;
  } catch (err) {
    console.warn('Failed to send Telegram message:', err);
    return undefined;
  }
}

async function editTelegramMessage(
  chatId: number,
  messageId: number,
  text: string,
  replyMarkup?: any
): Promise<void> {
  try {
    await telegramApi('editMessageText', {
      chat_id: chatId,
      message_id: messageId,
      text,
      parse_mode: 'HTML',
      disable_web_page_preview: true,
      reply_markup: replyMarkup,
    });
  } catch {
    // Ignore message not modified errors
  }
}

async function deleteTelegramMessageSafe(chatId: number, messageId: number): Promise<void> {
  try {
    await telegramApi('deleteMessage', {
      chat_id: chatId,
      message_id: messageId,
    });
  } catch {
    // Ignore delete errors
  }
}

function getActiveJobsList(chatId?: number | null): TransferJob[] {
  const allActive = transferJobs.filter(
    (j) =>
      j.status === 'downloading' ||
      j.status === 'uploading' ||
      j.status === 'queued' ||
      j.status === 'waiting_auth'
  );
  if (!chatId) return allActive;
  const isOwner = adminConfig.ownerChatId === chatId;
  if (isOwner) return allActive;
  const prof = getOrCreateUserProfile({ chatId, createIfMissing: false });
  const normEmail = prof?.userEmail ? prof.userEmail.trim().toLowerCase() : null;
  return allActive.filter(
    (j) => j.chatId === chatId || (normEmail && j.accountEmail?.toLowerCase() === normEmail)
  );
}

function getEffectiveSessionForChat(chatId?: number | null): {
  profile: UserDriveProfile;
  accessToken: string | null;
  userEmail: string | null;
  userName: string | null;
  activeFolderId: string | null;
  activeFolderName: string;
  accountEnabled: boolean;
  autoCategorizeByType: boolean;
  skipDuplicates: boolean;
  urlHandlingMode: 'ask' | 'to_drive' | 'to_telegram';
  defaultQuality: string;
  defaultCompressMode: CompressMode;
} {
  const prof =
    (chatId ? getOrCreateUserProfile({ chatId, createIfMissing: true }) : null) ||
    (driveSession.userEmail
      ? getOrCreateUserProfile({ email: driveSession.userEmail, createIfMissing: true })
      : null);

  if (prof && prof.accessToken) {
    return {
      profile: prof,
      accessToken: prof.accessToken,
      userEmail: prof.userEmail,
      userName: prof.userName,
      activeFolderId: prof.activeFolderId,
      activeFolderName: prof.activeFolderName || 'Telegram Bot Uploads',
      accountEnabled: prof.accountEnabled,
      autoCategorizeByType: prof.autoCategorizeByType,
      skipDuplicates: prof.skipDuplicates,
      urlHandlingMode: prof.urlHandlingMode || 'ask',
      defaultQuality: prof.defaultQuality || '720',
      defaultCompressMode: prof.defaultCompressMode || 'none',
    };
  }

  // If this is the owner or fallback when user hasn't linked a separate Drive yet
  const isOwner = !chatId || chatId === adminConfig.ownerChatId;
  if (isOwner && driveSession.accessToken) {
    const fallbackProf =
      prof ||
      ({
        profileId: 'default',
        accessToken: driveSession.accessToken,
        userEmail: driveSession.userEmail,
        userName: driveSession.userName,
        chatId: chatId || adminConfig.ownerChatId,
        linkCode: 'OWNER1',
        activeFolderId: driveSession.activeFolderId,
        activeFolderName: driveSession.activeFolderName || 'Telegram Bot Uploads',
        accountEnabled: adminConfig.accountEnabled,
        autoCategorizeByType,
        skipDuplicates,
        urlHandlingMode: adminConfig.urlHandlingMode || 'ask',
        defaultQuality: adminConfig.defaultQuality || '720',
        defaultCompressMode: adminConfig.defaultCompressMode || 'none',
        lastSyncedAt: driveSession.lastSyncedAt,
      } as UserDriveProfile);

    return {
      profile: fallbackProf,
      accessToken: driveSession.accessToken,
      userEmail: driveSession.userEmail,
      userName: fallbackProf.userName || driveSession.userName,
      activeFolderId: fallbackProf.activeFolderId || driveSession.activeFolderId,
      activeFolderName: fallbackProf.activeFolderName || driveSession.activeFolderName || 'Telegram Bot Uploads',
      accountEnabled: fallbackProf.accountEnabled ?? adminConfig.accountEnabled,
      autoCategorizeByType: fallbackProf.autoCategorizeByType ?? autoCategorizeByType,
      skipDuplicates: fallbackProf.skipDuplicates ?? skipDuplicates,
      urlHandlingMode: fallbackProf.urlHandlingMode || adminConfig.urlHandlingMode || 'ask',
      defaultQuality: fallbackProf.defaultQuality || adminConfig.defaultQuality || '720',
      defaultCompressMode: fallbackProf.defaultCompressMode || adminConfig.defaultCompressMode || 'none',
    };
  }

  const emptyProf =
    prof ||
    ({
      profileId: `chat_${chatId || 0}`,
      accessToken: null,
      userEmail: null,
      userName: null,
      chatId: chatId || null,
      linkCode: generateLinkCode(),
      activeFolderId: null,
      activeFolderName: 'Telegram Bot Uploads',
      accountEnabled: true,
      autoCategorizeByType: false,
      skipDuplicates: true,
      urlHandlingMode: 'ask',
      defaultQuality: '720',
      defaultCompressMode: 'none',
      lastSyncedAt: null,
    } as UserDriveProfile);

  return {
    profile: emptyProf,
    accessToken: null,
    userEmail: emptyProf.userEmail,
    userName: emptyProf.userName,
    activeFolderId: emptyProf.activeFolderId,
    activeFolderName: emptyProf.activeFolderName || 'Telegram Bot Uploads',
    accountEnabled: emptyProf.accountEnabled,
    autoCategorizeByType: emptyProf.autoCategorizeByType,
    skipDuplicates: emptyProf.skipDuplicates,
    urlHandlingMode: emptyProf.urlHandlingMode || 'ask',
    defaultQuality: emptyProf.defaultQuality || '720',
    defaultCompressMode: emptyProf.defaultCompressMode || 'none',
  };
}

function renderProgressBar(pct: number): string {
  const clamped = Math.max(0, Math.min(100, pct));
  const filled = Math.round(clamped / 10);
  return '█'.repeat(filled) + '░'.repeat(10 - filled);
}

function buildMainControlKeyboard(chatId?: number) {
  const sess = getEffectiveSessionForChat(chatId);
  const userJobs = getJobsForUser(sess.profile, !chatId || chatId === adminConfig.ownerChatId);
  const activeJobsCount = getActiveJobsList(chatId).length;
  const failedOrCancelledCount = userJobs.filter(
    (j) => j.status === 'failed' || j.status === 'cancelled'
  ).length;
  const isOwner = !adminConfig.ownerChatId || adminConfig.ownerChatId === chatId;
  const personalUrl = getAppUrl(chatId);

  const rows: any[][] = [];

  // Primary CTA if personal Google Drive is not yet linked
  if (!sess.accessToken && personalUrl && personalUrl.startsWith('https://')) {
    rows.push([
      {
        text: '🔗 ربط حسابي الشخصي بـ Google Drive الآن',
        url: personalUrl,
      },
    ]);
  }

  // Row 1: Pull from Drive & Pull from URL
  rows.push([
    { text: '📥 سحب ملف من حسابي Drive', callback_data: 'menu_pull_from_drive' },
    { text: '🌐 سحب فيديو/رابط لتليجرام', callback_data: 'prompt_url_to_telegram' },
  ]);

  // Row 2: Folder Selection & Creation
  rows.push([
    { text: '📁 تغيير مجلد الحفظ', callback_data: 'menu_folders' },
    { text: '➕ إنشاء مجلد جديد', callback_data: 'prompt_new_folder' },
  ]);

  // Row 3: Live Active Transfers & Recent Uploaded Files
  rows.push([
    {
      text: `📡 العمليات الجارية (${activeJobsCount})`,
      callback_data: 'view_active_transfers',
    },
    { text: '📄 ملفاتي المرفوعة', callback_data: 'list_recent_files' },
  ]);

  // Row 4: Personal Settings Portal & Owner Admin Portal
  if (isOwner) {
    rows.push([
      { text: '⚙️ إعدادات حسابي والجودة', callback_data: 'portal_settings' },
      { text: '🛡️ بوابة الإدارة (المالك)', callback_data: 'portal_admin' },
    ]);
  } else {
    rows.push([
      { text: '⚙️ إعدادات حسابي والجودة والضغط', callback_data: 'portal_settings' },
      { text: '🔄 تحديث لوحتي', callback_data: 'refresh_status' },
    ]);
  }

  if (activeJobsCount > 0) {
    rows.push([
      {
        text: `⛔ إلغاء الرفع الجاري (${activeJobsCount})`,
        callback_data: 'cancel_all_active',
      },
    ]);
  }

  if (failedOrCancelledCount > 0) {
    rows.push([
      {
        text: `🗑️ حذف الفاشلة (${failedOrCancelledCount})`,
        callback_data: 'clear_failed_jobs',
      },
      {
        text: `🔄 إعادة محاولة الفاشلة`,
        callback_data: 'retry_all_failed',
      },
    ]);
  }

  if (personalUrl && personalUrl.startsWith('https://')) {
    rows.push([
      {
        text: sess.accessToken
          ? '🌐 فتح مساحتي الشخصية في الموقع'
          : '🌐 فتح الموقع لتسجيل الدخول بحسابك الشخصي',
        url: personalUrl,
      },
    ]);
  }

  return { inline_keyboard: rows };
}

function buildControlPanelText(chatId?: number): string {
  const sess = getEffectiveSessionForChat(chatId);
  const userJobs = getJobsForUser(sess.profile, false);
  const completed = userJobs.filter((j) => j.status === 'completed');
  const totalBytes = completed.reduce((acc, j) => acc + (j.bytesTransferred || j.totalBytes || 0), 0);
  const activeCount = userJobs.filter((j) => j.status === 'downloading' || j.status === 'uploading').length;
  const waitingCount = userJobs.filter((j) => j.status === 'waiting_auth' || j.status === 'queued').length;
  const failedCount = userJobs.filter((j) => j.status === 'failed' || j.status === 'cancelled').length;

  let driveStatus = '🔴 غير مربوط بعد (اضغط زر الربط بالأسفل)';
  if (sess.accessToken) {
    driveStatus = sess.accountEnabled
      ? `🟢 <code>${sess.userEmail || 'متصل'}</code>`
      : `⏸️ <code>${sess.userEmail || 'متصل'}</code> (الاستقبال متوقف مؤقتاً)`;
  }

  const compressShort =
    sess.defaultCompressMode === 'zip'
      ? 'ضغط ZIP'
      : sess.defaultCompressMode === 'media'
      ? 'تقليص ميديا'
      : 'بدون ضغط';

  return (
    `☁️ <b>منصة النقل السحابي الشخصي | Telegram ⇄ Drive</b>\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    `👤 <b>بيانات حسابك الشخصي:</b>\n` +
    `• <b>حساب Google Drive:</b> ${driveStatus}\n` +
    `• <b>مجلد الحفظ النشط:</b> 📁 <code>${sess.activeFolderName}</code>\n` +
    `• <b>كود ربط الحساب بالموقع:</b> <code>${sess.profile.linkCode}</code>\n\n` +
    `⚡ <b>تفضيلات النقل السريع:</b>\n` +
    `• <b>الجودة والضغط:</b> <code>${sess.defaultQuality}p</code> · ${compressShort}\n` +
    `• <b>الفرز التلقائي:</b> ${sess.autoCategorizeByType ? 'مفعل ✅' : 'معطل ⚪'} | <b>منع التكرار:</b> ${
      sess.skipDuplicates ? 'مفعل ✅' : 'معطل ⚪'
    }\n` +
    `• <b>محرك الملفات الضخمة:</b> ${
      mtprotoConnected ? '🟢 MTProto Turbo (حتى 2GB)' : '⚪ قياسي (20MB)'
    }\n\n` +
    `📊 <b>إحصائيات حسابك:</b>\n` +
    `• المكتملة: <b>${completed.length}</b> ملف (<code>${formatBytes(totalBytes)}</code>)\n` +
    `• الجارية الآن: <b>${activeCount}</b> | بالانتظار: <b>${waitingCount}</b> | الفاشلة: <b>${failedCount}</b>\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    `💡 <i>أرسل أي ملف أو رابط (يوتيوب / تيك توك / مباشر) لتحويله فوراً، أو اختر من الأزرار:</i>`
  );
}

// 1. Settings Portal Builder (بوابة إعدادات الحساب الشخصي)
function buildSettingsPortalText(chatId?: number): string {
  const sess = getEffectiveSessionForChat(chatId);
  const isLinked = Boolean(sess.accessToken);
  const urlModeAr =
    sess.urlHandlingMode === 'ask'
      ? 'سؤال عند كل رابط (لتحديد الجودة والضغط والوجهة)'
      : sess.urlHandlingMode === 'to_drive'
      ? 'رفع تلقائي مباشر إلى Google Drive'
      : 'سحب وإرسال تلقائي إلى تليجرام';

  return (
    `⚙️ <b>بوابة إعدادات حسابك الشخصي</b>\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    `👤 <b>حالة الربط بـ Google Drive:</b>\n` +
    `• <b>الحالة:</b> ${isLinked ? '🟢 متصل ومربوط بحسابك' : '🔴 غير مربوط حالياً'}\n` +
    `• <b>البريد الإلكتروني:</b> <code>${sess.userEmail || 'غير محدد'}</code>\n` +
    `• <b>كود الربط السريع:</b> <code>${sess.profile.linkCode}</code>\n` +
    `• <b>حالة الاستقبال:</b> ${
      sess.accountEnabled ? '🟢 مفعّل (يستقبل ويرفع تلقائياً)' : '⏸️ متوقف مؤقتاً'
    }\n\n` +
    `🛠️ <b>تفضيلات الرفع والجودة والضغط:</b>\n` +
    `• <b>مجلد الحفظ:</b> 📁 <code>${sess.activeFolderName}</code>\n` +
    `• <b>جودة سحب الفيديو:</b> 🎬 <code>${sess.defaultQuality}p</code>\n` +
    `• <b>ضغط الملفات:</b> 📦 ${formatCompressModeAr(sess.defaultCompressMode)}\n` +
    `• <b>الفرز التلقائي للمجلدات:</b> ${sess.autoCategorizeByType ? 'مفعل ✅' : 'معطل ❌'}\n` +
    `• <b>منع تكرار الملفات:</b> ${sess.skipDuplicates ? 'مفعل ✅' : 'معطل ❌'}\n` +
    `• <b>سلوك الروابط المرسلة:</b> ${urlModeAr}\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    `👇 <b>اضغط على أي إعداد أدناه لتعديله فوراً لحسابك الشخصي:</b>`
  );
}

function buildSettingsPortalKeyboard(chatId?: number) {
  const sess = getEffectiveSessionForChat(chatId);
  const isLinked = Boolean(sess.accessToken);
  const personalUrl = getAppUrl(chatId);

  const urlModeBtnText =
    sess.urlHandlingMode === 'ask'
      ? '🔗 الروابط: سؤال عند كل رابط ⚡'
      : sess.urlHandlingMode === 'to_drive'
      ? '🔗 الروابط: رفع تلقائي لـ Drive ☁️'
      : '🔗 الروابط: إرسال تلقائي لتليجرام 📲';

  const compressBtnText =
    sess.defaultCompressMode === 'zip'
      ? '📦 الضغط الافتراضي: أرشيف ZIP (.zip) ✅'
      : sess.defaultCompressMode === 'media'
      ? '📦 الضغط الافتراضي: تقليص الميديا ✅'
      : '📦 الضغط الافتراضي: بدون ضغط ⚪';

  const rows: any[][] = [];

  if (personalUrl && personalUrl.startsWith('https://')) {
    rows.push([
      {
        text: isLinked
          ? '🔄 تبديل أو تحديث حسابي الشخصي في Google Drive'
          : '🔗 ربط حسابي الشخصي بـ Google Drive الآن',
        url: personalUrl,
      },
    ]);
  }

  if (isLinked) {
    rows.push([
      {
        text: sess.accountEnabled ? '⏸️ إيقاف الاستقبال مؤقتاً' : '▶️ تفعيل الاستقبال الآن',
        callback_data: 'toggle_account_enabled',
      },
      {
        text: '🔌 إلغاء ربط حسابي Drive',
        callback_data: 'confirm_unlink_drive',
      },
    ]);
  }

  rows.push([
    { text: '📁 تغيير مجلد الحفظ', callback_data: 'menu_folders' },
    { text: '➕ إنشاء مجلد جديد', callback_data: 'prompt_new_folder' },
  ]);

  rows.push([
    {
      text: `🎬 جودة السحب الافتراضية: ${sess.defaultQuality}p`,
      callback_data: 'cycle_default_quality',
    },
    {
      text: sess.autoCategorizeByType ? '🗂️ الفرز التلقائي: مفعل ✅' : '🗂️ الفرز التلقائي: معطل ⚪',
      callback_data: 'toggle_categorize',
    },
  ]);

  rows.push([
    {
      text: compressBtnText,
      callback_data: 'cycle_default_compress',
    },
  ]);

  rows.push([
    {
      text: sess.skipDuplicates
        ? '🛡️ منع تكرار الملفات في حسابي: مفعل ✅'
        : '🛡️ منع تكرار الملفات في حسابي: معطل ❌',
      callback_data: 'toggle_dedup',
    },
  ]);

  rows.push([{ text: urlModeBtnText, callback_data: 'toggle_url_mode' }]);
  rows.push([{ text: '🏠 العودة للقائمة الرئيسية', callback_data: 'open_main' }]);

  return { inline_keyboard: rows };
}

// 2. Owner Admin Portal Builder (بوابة الإدارة والتحكم للمالك)
function buildAdminPortalText(callerChatId?: number): string {
  const usersList = Object.values(adminConfig.knownUsers);
  const linkedProfilesCount = Object.values(userProfiles).filter((p) => p.accessToken).length;
  const activeList = getActiveJobsList();
  const isOwner = adminConfig.ownerChatId === callerChatId;

  return (
    `🛡️ <b>بوابة الإدارة المركزية (لمالك النظام)</b>\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    `👑 <b>صلاحيات المالك والوصول:</b>\n` +
    `• <b>مالك البوت:</b> ${
      adminConfig.ownerChatId
        ? `${adminConfig.ownerName || 'المالك'} (<code>${adminConfig.ownerChatId}</code>)${isOwner ? ' — أنت 👑' : ''}`
        : 'غير معيّن بعد (اضغط زر تعيين حسابك كمالك أدناه)'
    }\n` +
    `• <b>وضع الاستخدام:</b> ${
      adminConfig.accessMode === 'owner_only'
        ? '🔒 خاص بالمالك فقط'
        : '🌍 متاح لأي مستخدم عبر حسابه الشخصي'
    }\n` +
    `• <b>حالة البوت العامة:</b> ${adminConfig.botPaused ? '⏸️ متوقف مؤقتاً' : '🟢 يعمل بكامل طاقته'}\n\n` +
    `⚙️ <b>حالة المحركات والمستخدمين:</b>\n` +
    `• <b>محرك MTProto Turbo (2GB):</b> ${
      mtprotoConnected ? `🟢 متصل (${mtprotoPoolClients.length} جلسات متوازية)` : '🔴 غير متصل'
    }\n` +
    `• <b>الحسابات الشخصية المربوطة بـ Drive:</b> <b>${linkedProfilesCount}</b> حساب\n` +
    `• <b>إجمالي مستخدمي تليجرام:</b> <b>${usersList.length}</b> مستخدم\n` +
    `• <b>العمليات الجارية الآن:</b> <b>${activeList.length}</b> | <b>إجمالي السجل:</b> <b>${transferJobs.length}</b>\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    `👇 <b>تحكم في النظام والمستخدمين من الأزرار أدناه:</b>`
  );
}

function buildAdminPortalKeyboard(callerChatId?: number) {
  const activeCount = getActiveJobsList().length;
  const usersCount = Object.keys(adminConfig.knownUsers).length;

  const rows: any[][] = [
    [
      {
        text:
          adminConfig.ownerChatId === callerChatId
            ? '👑 أنت مالك البوت المعتمد ✅'
            : '👑 تعيين حسابي كمالك للبوت',
        callback_data: 'claim_owner',
      },
    ],
    [
      {
        text: adminConfig.botPaused ? '▶️ تشغيل البوت الآن' : '⏸️ إيقاف البوت مؤقتاً',
        callback_data: 'toggle_bot_power',
      },
      {
        text:
          adminConfig.accessMode === 'owner_only'
            ? '🔒 الوضع: خاص بالمالك فقط'
            : '🌍 الوضع: متاح لكل مستخدم بحسابه',
        callback_data: 'toggle_access_mode',
      },
    ],
    [
      {
        text: `📡 مراقبة جميع العمليات الجارية (${activeCount})`,
        callback_data: 'view_active_transfers',
      },
    ],
    [
      {
        text: `👥 إدارة المستخدمين (${usersCount})`,
        callback_data: 'admin_users_list',
      },
      {
        text: '⚡ تنشيط محرك MTProto 2GB',
        callback_data: 'admin_restart_mtproto',
      },
    ],
    [
      {
        text: '🗑️ حذف الفاشلة والملغاة',
        callback_data: 'clear_failed_jobs',
      },
      {
        text: '🧹 مسح كل سجل النظام',
        callback_data: 'admin_clear_all_history',
      },
    ],
    [{ text: '🏠 العودة للقائمة الرئيسية', callback_data: 'open_main' }],
  ];

  return { inline_keyboard: rows };
}

// 3. Active Transfers Live Monitor Builder (خيار إظهار عمليات الرفع الحالية)
function buildActiveTransfersText(chatId?: number): string {
  const activeList = getActiveJobsList(chatId);
  if (activeList.length === 0) {
    return (
      `📡 <b>مراقب العمليات والتحويلات الجارية</b>\n` +
      `━━━━━━━━━━━━━━━━━━━━━━\n` +
      `✅ <b>لا توجد أي عمليات رفع أو سحب جارية في هذه اللحظة.</b>\n\n` +
      `💡 أرسل أي ملف أو رابط لرفعه فوراً إلى حسابك في Google Drive، أو اسحب ملفاتك من Drive إلى تليجرام.`
    );
  }

  const lines = activeList.map((job, i) => {
    const pct =
      job.totalBytes > 0 ? Math.min(99, Math.round((job.bytesTransferred / job.totalBytes) * 100)) : 0;
    const dirLabel =
      job.direction === 'to_telegram' || job.source === 'drive_to_telegram' || job.source === 'url_to_telegram'
        ? '📲 سحب إلى تليجرام'
        : '☁️ رفع إلى Google Drive';
    const statusAr =
      job.status === 'downloading'
        ? 'جاري السحب...'
        : job.status === 'uploading'
        ? 'جاري الرفع...'
        : job.status === 'waiting_auth'
        ? 'بانتظار ربط Drive'
        : 'في الطابور';

    return (
      `<b>${i + 1}. 📄 ${job.fileName}</b>\n` +
      `   • المسار: ${dirLabel} (${statusAr})\n` +
      `   • التقدم: <code>[${renderProgressBar(pct)}] ${pct}%</code>\n` +
      `   • المنقول: <code>${formatBytes(job.bytesTransferred)}</code>${
        job.totalBytes > 0 ? ` من <code>${formatBytes(job.totalBytes)}</code>` : ''
      }\n` +
      `   • السرعة: 🚀 <code>${job.speedBps > 0 ? `${formatBytes(job.speedBps)}/s` : 'جاري القياس...'}</code>`
    );
  });

  return (
    `📡 <b>عمليات النقل الجارية حالياً (${activeList.length} نشطة):</b>\n` +
    `━━━━━━━━━━━━━━━━━━━━━━\n` +
    lines.join('\n\n') +
    `\n━━━━━━━━━━━━━━━━━━━━━━\n` +
    `👇 يمكنك إلغاء أي عملية فورا أو تحديث نسبة التقدم:`
  );
}

function buildActiveTransfersKeyboard(chatId?: number) {
  const activeList = getActiveJobsList(chatId);
  const rows: any[][] = [];

  for (const job of activeList.slice(0, 8)) {
    const shortName = job.fileName.length > 26 ? job.fileName.slice(0, 24) + '…' : job.fileName;
    rows.push([
      {
        text: `⛔ إلغاء: ${shortName}`,
        callback_data: `cancel_${job.id}`,
      },
    ]);
  }

  if (activeList.length > 1) {
    rows.push([
      {
        text: `⛔ إلغاء جميع العمليات الجارية (${activeList.length})`,
        callback_data: 'cancel_all_active',
      },
    ]);
  }

  rows.push([
    { text: '🔄 تحديث التقدم الآن', callback_data: 'view_active_transfers' },
    { text: '🏠 القائمة الرئيسية', callback_data: 'open_main' },
  ]);

  return { inline_keyboard: rows };
}

// ============================================================================
// Cancellation & Cleanup Logic
// ============================================================================

function cancelTransferJobById(jobId: string): TransferJob | null {
  const job = transferJobs.find((j) => j.id === jobId);
  if (!job) return null;

  const controller = jobAbortControllers.get(jobId);
  if (controller) {
    controller.abort();
    jobAbortControllers.delete(jobId);
  }

  if (
    job.status === 'downloading' ||
    job.status === 'uploading' ||
    job.status === 'queued' ||
    job.status === 'waiting_auth'
  ) {
    job.status = 'cancelled';
    job.speedBps = 0;
    job.errorMessage = 'تم إلغاء رفع الملف بناءً على طلب المستخدم.';
    saveStateToDisk();

    if (job.chatId && job.statusMessageId) {
      editTelegramMessage(
        job.chatId,
        job.statusMessageId,
        `🚫 <b>تم إلغاء العملية</b>\n\n📄 <b>الملف:</b> <code>${job.fileName}</code>`,
        {
          inline_keyboard: [
            [
              { text: '🔄 إعادة المحاولة', callback_data: `retry_${job.id}` },
              { text: '🗑️ حذف من السجل', callback_data: `delete_${job.id}` },
            ],
            [{ text: '🏠 القائمة الرئيسية', callback_data: 'open_main' }],
          ],
        }
      );
    }
  }

  return job;
}

function clearAllFailedAndCancelledJobs(chatId?: number | null, accountEmail?: string | null): number {
  let removed = 0;
  const normEmail = accountEmail ? accountEmail.trim().toLowerCase() : null;
  const isOwner = !chatId || chatId === adminConfig.ownerChatId;

  for (let i = transferJobs.length - 1; i >= 0; i--) {
    const j = transferJobs[i];
    if (j.status === 'failed' || j.status === 'cancelled') {
      const matchesUser =
        isOwner ||
        (chatId && j.chatId === chatId) ||
        (normEmail && j.accountEmail?.toLowerCase() === normEmail);
      if (matchesUser) {
        transferJobs.splice(i, 1);
        removed++;
      }
    }
  }
  if (removed > 0) {
    saveStateToDisk();
  }
  return removed;
}

// ============================================================================
// Google Drive Helper Functions & Deduplication Check
// ============================================================================

let folderMutex: Promise<any> = Promise.resolve();

async function ensureDriveFolder(token: string, folderName: string, parentId?: string | null): Promise<{ id: string; name: string }> {
  const run = async () => {
    const escapedName = folderName.replace(/'/g, "\\'");
    let q = `mimeType='application/vnd.google-apps.folder' and name='${escapedName}' and trashed=false`;
    if (parentId) {
      q += ` and '${parentId}' in parents`;
    }

    const searchUrl = `https://www.googleapis.com/drive/v3/files?q=${encodeURIComponent(q)}&fields=files(id,name)&pageSize=1`;
    const searchRes = await fetch(searchUrl, {
      headers: { Authorization: `Bearer ${token}` },
    });

    if (!searchRes.ok) {
      if (searchRes.status === 401 || searchRes.status === 403) {
        throw new Error('انتهت صلاحية جلسة Google Drive. افتح رابط الموقع لتنشيط الاتصال بحسابك.');
      }
      const errText = await searchRes.text();
      throw new Error(`فشل الاتصال بـ Google Drive (${searchRes.status}): ${errText}`);
    }

    const searchData = await searchRes.json();
    if (searchData.files && searchData.files.length > 0) {
      return { id: searchData.files[0].id, name: searchData.files[0].name };
    }

    const createRes = await fetch('https://www.googleapis.com/drive/v3/files?fields=id,name', {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${token}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        name: folderName,
        mimeType: 'application/vnd.google-apps.folder',
        parents: parentId ? [parentId] : undefined,
      }),
    });

    if (!createRes.ok) {
      const errText = await createRes.text();
      throw new Error(`تعذر إنشاء مجلد في Google Drive: ${errText}`);
    }

    return await createRes.json();
  };

  const resultPromise = folderMutex.then(run, run);
  folderMutex = resultPromise.catch(() => {});
  return resultPromise;
}

// Check if an identical file already exists in the same Google Drive account & folder
async function findExistingDuplicateForAccount(
  job: TransferJob,
  token: string,
  targetFolderId: string | null,
  skipDupEnabled: boolean = true
): Promise<{ id: string; name: string; webViewLink?: string; size?: number } | null> {
  if (!skipDupEnabled) return null;

  const currentAccount = (job.accountEmail || driveSession.userEmail || 'default').toLowerCase();

  // 1. Check in-memory completed jobs for the same Google account
  const completedDuplicate = transferJobs.find((existing) => {
    if (existing.id === job.id || existing.status !== 'completed' || !existing.driveFileId) return false;
    if (existing.accountEmail && existing.accountEmail.toLowerCase() !== currentAccount) return false;

    // Match by Telegram unique file ID
    if (
      job.telegramFileUniqueId &&
      existing.telegramFileUniqueId &&
      job.telegramFileUniqueId === existing.telegramFileUniqueId
    ) {
      return true;
    }

    // Match by exact file name and size
    if (
      existing.fileName === job.fileName &&
      job.totalBytes > 0 &&
      Math.abs((existing.totalBytes || 0) - job.totalBytes) < 16
    ) {
      return true;
    }

    return false;
  });

  if (completedDuplicate && completedDuplicate.driveFileId) {
    // Verify file still exists (not trashed) in Google Drive
    try {
      const checkRes = await fetch(
        `https://www.googleapis.com/drive/v3/files/${completedDuplicate.driveFileId}?fields=id,name,size,trashed,webViewLink`,
        {
          headers: { Authorization: `Bearer ${token}` },
        }
      );
      if (checkRes.ok) {
        const fileData = await checkRes.json();
        if (!fileData.trashed) {
          return {
            id: fileData.id,
            name: fileData.name,
            webViewLink:
              fileData.webViewLink || `https://drive.google.com/file/d/${fileData.id}/view`,
            size: fileData.size ? parseInt(fileData.size, 10) : completedDuplicate.totalBytes,
          };
        }
      }
    } catch {
      // Fall through to Drive query search
    }
  }

  // 2. Query Google Drive directly for a file with the same name in the target folder
  try {
    const escapedName = job.fileName.replace(/\\/g, '\\\\').replace(/'/g, "\\'");
    let q = `name = '${escapedName}' and mimeType != 'application/vnd.google-apps.folder' and trashed = false`;
    if (targetFolderId) {
      q += ` and '${targetFolderId}' in parents`;
    }

    const searchUrl = `https://www.googleapis.com/drive/v3/files?q=${encodeURIComponent(
      q
    )}&fields=files(id,name,size,webViewLink)&pageSize=5`;
    const res = await fetch(searchUrl, {
      headers: { Authorization: `Bearer ${token}` },
    });

    if (res.ok) {
      const data = await res.json();
      const files: any[] = data.files || [];
      for (const f of files) {
        const fSize = f.size ? parseInt(f.size, 10) : 0;
        if (!job.totalBytes || job.totalBytes === 0 || fSize === 0 || Math.abs(fSize - job.totalBytes) < 64) {
          return {
            id: f.id,
            name: f.name,
            webViewLink: f.webViewLink || `https://drive.google.com/file/d/${f.id}/view`,
            size: fSize || job.totalBytes,
          };
        }
      }
    }
  } catch {
    // Ignore Drive search error and proceed with normal upload
  }

  return null;
}

async function listDriveFolders(token: string): Promise<{ id: string; name: string }[]> {
  const q = encodeURIComponent("mimeType = 'application/vnd.google-apps.folder' and trashed = false");
  const orderBy = encodeURIComponent('createdTime desc');
  const res = await fetch(
    `https://www.googleapis.com/drive/v3/files?q=${q}&pageSize=12&orderBy=${orderBy}&fields=files(id,name)`,
    {
      headers: { Authorization: `Bearer ${token}` },
    }
  );
  if (!res.ok) {
    throw new Error('تعذر جلب قائمة المجلدات من Google Drive.');
  }
  const data = await res.json();
  return data.files || [];
}

function getSubfolderNameForMime(mimeType: string): string {
  if (mimeType.startsWith('video/')) return 'الفيديوهات - Videos';
  if (mimeType.startsWith('image/')) return 'الصور - Photos';
  if (mimeType.startsWith('audio/')) return 'الصوتيات - Audio';
  if (
    mimeType.includes('pdf') ||
    mimeType.includes('document') ||
    mimeType.includes('msword') ||
    mimeType.includes('spreadsheet') ||
    mimeType.includes('presentation') ||
    mimeType.startsWith('text/')
  ) {
    return 'المستندات - Documents';
  }
  if (mimeType.includes('zip') || mimeType.includes('rar') || mimeType.includes('tar') || mimeType.includes('7z') || mimeType.includes('compressed')) {
    return 'الأرشيف والملفات المضغوطة - Archives';
  }
  return 'ملفات أخرى - Others';
}

async function createResumableUploadSession(
  token: string,
  fileName: string,
  mimeType: string,
  folderId: string | null,
  description: string,
  signal?: AbortSignal
): Promise<string> {
  const headers: Record<string, string> = {
    Authorization: `Bearer ${token}`,
    'Content-Type': 'application/json; charset=UTF-8',
    'X-Upload-Content-Type': mimeType || 'application/octet-stream',
  };

  const initRes = await fetch(
    'https://www.googleapis.com/upload/drive/v3/files?uploadType=resumable&fields=id,name,size,mimeType,webViewLink,webContentLink,createdTime',
    {
      method: 'POST',
      headers,
      body: JSON.stringify({
        name: fileName,
        parents: folderId ? [folderId] : undefined,
        description,
      }),
      signal,
    }
  );

  if (!initRes.ok) {
    const errBody = await initRes.text();
    throw new Error(`فشل بدء جلسة الرفع في Google Drive (${initRes.status}): ${errBody}`);
  }

  const sessionUri = initRes.headers.get('location');
  if (!sessionUri) {
    throw new Error('لم يُرجع Google Drive رابط جلسة الرفع (Location Header).');
  }

  return sessionUri;
}

// ============================================================================
// Multi-Platform Video & Link Resolver (YouTube, TikTok, Drive, MediaFire, etc.)
// ============================================================================

const SAVETUBE_SECRET_KEY = 'C5D58EF67A7584E4A29F6C35BBC4EB12';

function decodeSaveTubePayload(encodedBase64: string): any {
  const data = Buffer.from(encodedBase64, 'base64');
  const iv = data.slice(0, 16);
  const content = data.slice(16);
  const key = Buffer.from(SAVETUBE_SECRET_KEY, 'hex');
  const decipher = createDecipheriv('aes-128-cbc', key, iv);
  const decrypted = Buffer.concat([decipher.update(content), decipher.final()]);
  return JSON.parse(decrypted.toString('utf8'));
}

function extractCleanHttpUrl(rawInput: string): string {
  const trimmed = (rawInput || '').trim();
  const match = trimmed.match(/https?:\/\/[^\s"'<>]+/i);
  return match ? match[0] : trimmed;
}

function extractYouTubeId(urlStr: string): string | null {
  const clean = extractCleanHttpUrl(urlStr);
  try {
    const withProto = /^https?:\/\//i.test(clean) ? clean : `https://${clean}`;
    const parsed = new URL(withProto);
    const host = parsed.hostname.toLowerCase();

    if (host === 'youtu.be' || host.endsWith('.youtu.be')) {
      const seg = parsed.pathname.split('/').filter(Boolean)[0];
      if (seg && /^[a-zA-Z0-9_-]{11}$/.test(seg)) {
        return seg;
      }
    }

    if (host.includes('youtube.com') || host.includes('youtube-nocookie.com')) {
      const vParam = parsed.searchParams.get('v') || parsed.searchParams.get('vi');
      if (vParam && /^[a-zA-Z0-9_-]{11}$/.test(vParam)) {
        return vParam;
      }
      const pathMatch = parsed.pathname.match(
        /\/(?:shorts|live|embed|v|e|watch|reels)\/([a-zA-Z0-9_-]{11})/i
      );
      if (pathMatch && pathMatch[1]) {
        return pathMatch[1];
      }
    }
  } catch {
    // Fallback to regex below
  }

  const vQueryMatch = clean.match(/[?&]v=([a-zA-Z0-9_-]{11})/i);
  if (vQueryMatch && vQueryMatch[1]) return vQueryMatch[1];

  const regex =
    /(?:youtube\.com\/(?:shorts\/|live\/|embed\/|v\/|watch\?v=)|youtu\.be\/)([a-zA-Z0-9_-]{11})/i;
  const match = clean.match(regex);
  return match ? match[1] : null;
}

function sanitizeMediaTitle(rawTitle: string, fallbackPrefix: string): string {
  const cleaned = (rawTitle || '')
    .replace(/[\\/:*?"<>|\r\n]+/g, ' ')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 95);
  return cleaned || `${fallbackPrefix}_${Date.now()}`;
}

export function detectVideoPlatform(rawUrl: string): {
  isVideoPlatform: boolean;
  platformName: string;
  isYouTube: boolean;
  isTikTok: boolean;
} {
  try {
    const clean = extractCleanHttpUrl(rawUrl);
    const host = new URL(clean).hostname.toLowerCase();
    if (host.includes('youtube.com') || host === 'youtu.be' || host.endsWith('.youtu.be')) {
      return { isVideoPlatform: true, platformName: 'YouTube (يوتيوب)', isYouTube: true, isTikTok: false };
    }
    if (host.includes('tiktok.com')) {
      return { isVideoPlatform: true, platformName: 'TikTok (تيك توك بدون علامة مائية)', isYouTube: false, isTikTok: true };
    }
    if (
      host.includes('instagram.com') ||
      host.includes('facebook.com') ||
      host.includes('fb.watch') ||
      host.includes('twitter.com') ||
      host.includes('x.com')
    ) {
      return { isVideoPlatform: true, platformName: 'فيديو تواصل اجتماعي', isYouTube: false, isTikTok: false };
    }
  } catch {
    // Ignore invalid URL
  }
  return { isVideoPlatform: false, platformName: '', isYouTube: false, isTikTok: false };
}

async function resolveYouTubeStream(
  rawUrl: string,
  format: 'video' | 'audio' = 'video',
  preferredQuality?: string
): Promise<{
  resolvedUrl: string;
  detectedFileName: string;
  detectedMimeType: string;
  customHeaders?: Record<string, string>;
}> {
  const videoId = extractYouTubeId(rawUrl);
  if (!videoId) {
    throw new Error('لم يتم التعرف على معرف فيديو يوتيوب (Video ID) من الرابط المرسل.');
  }

  const normalizedYtUrl = `https://www.youtube.com/watch?v=${videoId}`;
  const ua =
    'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/133.0.0.0 Mobile Safari/537.36';

  const defaultAudioQualities = ['320', '192', '128', '256', '92'];
  const defaultVideoQualities = ['720', '480', '360', '1080', '240', '144'];
  const baseOrder = format === 'audio' ? defaultAudioQualities : defaultVideoQualities;
  const cleanPref = (preferredQuality || '').replace(/[^0-9]/g, '');
  const initialQualities = cleanPref
    ? [cleanPref, ...baseOrder.filter((q) => q !== cleanPref)]
    : baseOrder;

  let lastError = '';
  for (let attempt = 0; attempt < 2; attempt++) {
    try {
      const cdnRes = await fetch('https://media.savetube.vip/api/random-cdn', {
        signal: AbortSignal.timeout(8000),
      });
      if (!cdnRes.ok) {
        throw new Error(`SaveTube CDN status ${cdnRes.status}`);
      }
      const { cdn } = await cdnRes.json();
      if (!cdn) {
        throw new Error('لم يتوفر خادم CDN لتحويل يوتيوب');
      }

      const infoRes = await fetch(`https://${cdn}/v2/info`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'User-Agent': ua,
          Referer: 'https://save-tube.com/',
        },
        body: JSON.stringify({ url: normalizedYtUrl }),
        signal: AbortSignal.timeout(12000),
      });

      const infoJson = await infoRes.json();
      if (!infoJson?.data) {
        throw new Error(infoJson?.message || 'تعذر قراءة بيانات فيديو يوتيوب.');
      }

      const decoded = decodeSaveTubePayload(infoJson.data);
      const safeTitle = sanitizeMediaTitle(decoded.title, `YouTube_${videoId}`);

      const advertisedQualities: string[] = [];
      if (format === 'audio' && Array.isArray(decoded.audio_formats)) {
        for (const af of decoded.audio_formats) {
          if (af?.quality) advertisedQualities.push(String(af.quality));
        }
      } else if (format === 'video' && Array.isArray(decoded.video_formats)) {
        for (const vf of decoded.video_formats) {
          if (vf?.quality) advertisedQualities.push(String(vf.quality));
          else if (vf?.height) advertisedQualities.push(String(vf.height));
        }
      }

      const uniqueQualities = Array.from(new Set([...initialQualities, ...advertisedQualities]));

      for (const q of uniqueQualities) {
        const dlRes = await fetch(`https://${cdn}/download`, {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
            'User-Agent': ua,
            Referer: 'https://save-tube.com/',
          },
          body: JSON.stringify({
            downloadType: format === 'audio' ? 'audio' : 'video',
            quality: q,
            key: decoded.key,
          }),
          signal: AbortSignal.timeout(15000),
        });

        const dlJson = await dlRes.json();
        const downloadUrl = dlJson?.data?.downloadUrl;
        if (downloadUrl && typeof downloadUrl === 'string' && downloadUrl.startsWith('http')) {
          const isAudio = format === 'audio';
          const badge = cleanPref || q;
          return {
            resolvedUrl: downloadUrl,
            detectedFileName: isAudio ? `${safeTitle} (${badge}kbps).mp3` : `${safeTitle} (${badge}p).mp4`,
            detectedMimeType: isAudio ? 'audio/mpeg' : 'video/mp4',
            customHeaders: {
              'User-Agent': ua,
              Referer: 'https://save-tube.com/',
            },
          };
        }
      }
    } catch (err: any) {
      lastError = err?.message || 'خطأ في استخراج فيديو يوتيوب';
    }
  }

  // Fallback to standalone yt-dlp binary if SaveTube fails
  try {
    return await resolveWithYtDlpBinary(normalizedYtUrl, format, preferredQuality);
  } catch (ytDlpErr: any) {
    console.warn('yt-dlp fallback failed for YouTube URL:', ytDlpErr?.message);
  }

  throw new Error(`تعذر سحب فيديو يوتيوب حالياً (${lastError}). تأكد من أن الفيديو عام وليس خاصاً.`);
}

async function resolveTikTokStream(
  rawUrl: string,
  format: 'video' | 'audio' = 'video',
  preferredQuality?: string
): Promise<{
  resolvedUrl: string;
  detectedFileName: string;
  detectedMimeType: string;
  customHeaders?: Record<string, string>;
}> {
  // 1. Primary: TikWM API (Fast, HD, No Watermark)
  try {
    const apiRes = await fetch(`https://www.tikwm.com/api/?hd=1&url=${encodeURIComponent(rawUrl)}`, {
      headers: {
        'User-Agent':
          'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
      },
      signal: AbortSignal.timeout(12000),
    });

    if (apiRes.ok) {
      const json = await apiRes.json();
      if (json.code === 0 && json.data) {
        const d = json.data;
        const safeTitle = sanitizeMediaTitle(d.title || d.author?.unique_id || d.id, `TikTok_${d.id || Date.now()}`);

        if (format === 'audio' && d.music) {
          return {
            resolvedUrl: d.music,
            detectedFileName: `${safeTitle}.mp3`,
            detectedMimeType: 'audio/mpeg',
            customHeaders: { Referer: 'https://www.tiktok.com/' },
          };
        }

        const cleanQ = (preferredQuality || '720').replace(/[^0-9]/g, '');
        const wantsHighHd = cleanQ === '1080' || cleanQ === '720';
        const videoUrl = wantsHighHd ? d.hdplay || d.play || d.wmplay : d.play || d.hdplay || d.wmplay;
        if (videoUrl) {
          const qBadge = wantsHighHd && d.hdplay ? 'HD' : 'SD';
          return {
            resolvedUrl: videoUrl,
            detectedFileName: `${safeTitle} (${qBadge}).mp4`,
            detectedMimeType: 'video/mp4',
            customHeaders: { Referer: 'https://www.tiktok.com/' },
          };
        }
      }
    }
  } catch (err: any) {
    console.warn('TikWM primary extractor warning, trying yt-dlp fallback:', err?.message);
  }

  // 2. Fallback: yt-dlp standalone binary
  return resolveWithYtDlpBinary(rawUrl, format, preferredQuality);
}

async function resolveWithYtDlpBinary(
  rawUrl: string,
  format: 'video' | 'audio' = 'video',
  preferredQuality?: string
): Promise<{
  resolvedUrl: string;
  detectedFileName: string;
  detectedMimeType: string;
}> {
  const candidates = [path.join(process.cwd(), 'bin', 'yt-dlp'), '/tmp/yt-dlp'];
  let binPath = candidates.find((p) => fs.existsSync(p));

  if (!binPath) {
    const dlRes = await fetch('https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux');
    if (dlRes.ok && dlRes.body) {
      const buf = Buffer.from(await dlRes.arrayBuffer());
      fs.writeFileSync('/tmp/yt-dlp', buf, { mode: 0o755 });
      binPath = '/tmp/yt-dlp';
    }
  }

  if (!binPath) {
    throw new Error('محرك yt-dlp غير متوفر لاستخراج هذا الرابط.');
  }

  const cleanQ = parseInt((preferredQuality || '720').replace(/[^0-9]/g, ''), 10);
  const heightFilter = !isNaN(cleanQ) && cleanQ >= 144 && cleanQ <= 2160 ? `[height<=${cleanQ}]` : '';
  const formatSelector =
    format === 'audio'
      ? 'bestaudio/best'
      : heightFilter
      ? `best${heightFilter}[ext=mp4]/best${heightFilter}/best[ext=mp4]/best`
      : 'best[ext=mp4]/best';

  const { stdout } = await execFileAsync(
    binPath,
    ['--no-playlist', '-f', formatSelector, '--print', '%(title)s\n%(ext)s\n%(url)s', rawUrl],
    { timeout: 20000 }
  );

  const lines = stdout
    .split('\n')
    .map((l) => l.trim())
    .filter(Boolean);
  if (lines.length < 3) {
    throw new Error('لم يتمكن المحرك من استخراج رابط البث المباشر للفيديو.');
  }

  const rawTitle = lines[0];
  const ext = format === 'audio' ? 'mp3' : lines[1] || 'mp4';
  const directStreamUrl = lines[lines.length - 1];
  const safeTitle = sanitizeMediaTitle(rawTitle, 'Video');

  return {
    resolvedUrl: directStreamUrl,
    detectedFileName: `${safeTitle}.${ext}`,
    detectedMimeType: format === 'audio' ? 'audio/mpeg' : 'video/mp4',
  };
}

async function resolveTelegramPostLinkIfApplicable(
  rawUrl: string,
  mediaFormat: 'video' | 'audio' = 'video',
  preferredQuality?: string
): Promise<{
  resolvedUrl: string;
  detectedFileName?: string;
  detectedMimeType?: string;
  customHeaders?: Record<string, string>;
}> {
  const cleanedInputUrl = extractCleanHttpUrl(rawUrl);
  try {
    const parsed = new URL(cleanedInputUrl);
    const host = parsed.hostname.toLowerCase();
    const effectiveQuality = preferredQuality || adminConfig.defaultQuality || '720';

    // 0A. YouTube Links (watch, shorts, youtu.be, live, music.youtube.com)
    if (host.includes('youtube.com') || host === 'youtu.be' || host.endsWith('.youtu.be')) {
      return await resolveYouTubeStream(cleanedInputUrl, mediaFormat, effectiveQuality);
    }

    // 0B. TikTok Links (tiktok.com, vm.tiktok.com, vt.tiktok.com)
    if (host.includes('tiktok.com')) {
      return await resolveTikTokStream(cleanedInputUrl, mediaFormat, effectiveQuality);
    }

    // 0C. Other Social Video Links (Instagram, Facebook, X/Twitter) via yt-dlp
    if (
      host.includes('instagram.com') ||
      host.includes('facebook.com') ||
      host.includes('fb.watch') ||
      host.includes('twitter.com') ||
      host.includes('x.com')
    ) {
      return await resolveWithYtDlpBinary(cleanedInputUrl, mediaFormat, effectiveQuality);
    }

    // 1. Dropbox shared links -> force direct download (dl=1)
    if (host.includes('dropbox.com')) {
      parsed.searchParams.set('dl', '1');
      return { resolvedUrl: parsed.toString() };
    }

    // 2. Google Drive public shared links -> direct download endpoint
    if (host.includes('drive.google.com')) {
      const fileIdMatch = parsed.pathname.match(/\/file\/d\/([a-zA-Z0-9_-]+)/);
      const queryId = parsed.searchParams.get('id');
      const fileId = fileIdMatch ? fileIdMatch[1] : queryId;
      if (fileId) {
        return {
          resolvedUrl: `https://drive.google.com/uc?export=download&id=${fileId}&confirm=t`,
        };
      }
    }

    // 3. GitHub blob links -> raw.githubusercontent.com
    if (host === 'github.com' && parsed.pathname.includes('/blob/')) {
      const rawPath = parsed.pathname.replace('/blob/', '/');
      return {
        resolvedUrl: `https://raw.githubusercontent.com${rawPath}`,
      };
    }

    // 4. Pixeldrain file links (pixeldrain.com/u/ID -> pixeldrain.com/api/file/ID?download)
    if (host.includes('pixeldrain.com')) {
      const pdMatch = parsed.pathname.match(/\/u\/([a-zA-Z0-9_-]+)/);
      if (pdMatch && pdMatch[1]) {
        return {
          resolvedUrl: `https://pixeldrain.com/api/file/${pdMatch[1]}?download`,
        };
      }
    }

    // 5. MediaFire file share links -> scrape direct download button URL
    if (host.includes('mediafire.com') && parsed.pathname.startsWith('/file/')) {
      const mfRes = await fetch(rawUrl, {
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
        },
      });
      if (mfRes.ok) {
        const html = await mfRes.text();
        const directMatch =
          html.match(/href="(https?:\/\/download\d*\.mediafire\.com\/[^"]+)"/i) ||
          html.match(/id="downloadButton"[^>]+href="(https?:\/\/[^"]+)"/i);
        if (directMatch && directMatch[1]) {
          const directHref = directMatch[1];
          const urlParts = directHref.split('/');
          const candidateName = decodeURIComponent(urlParts[urlParts.length - 1] || '');
          return {
            resolvedUrl: directHref,
            detectedFileName: candidateName || undefined,
          };
        }
      }
    }

    // 6. OneDrive shared links -> append download=1
    if (host.includes('1drv.ms') || host.includes('onedrive.live.com')) {
      parsed.searchParams.set('download', '1');
      return { resolvedUrl: parsed.toString() };
    }

    // 7. Telegram Post Links (t.me/...)
    if (host !== 't.me' && host !== 'telegram.me') {
      return { resolvedUrl: rawUrl };
    }

    const parts = parsed.pathname.split('/').filter(Boolean);
    if (parts[0] === 'c') {
      throw new Error(
        `هذا رابط منشور داخل قناة/مجموعة تليجرام خاصة. لرفع هذا الملف إلى Google Drive، افتح المنشور في تطبيق تليجرام واعمل له تحويل (Forward) مباشرة إلى البوت @${botInfo?.username || 'UMED_TD_bot'}.`
      );
    }

    if (parts.length >= 2) {
      const channelUsername = parts[0];
      const messageId = parts[parts.length - 1];
      if (/^\d+$/.test(messageId)) {
        const embedUrl = `https://t.me/${channelUsername}/${messageId}?embed=1`;
        const embedRes = await fetch(embedUrl);
        if (embedRes.ok) {
          const html = await embedRes.text();

          const docTitleMatch = html.match(/class="tgme_widget_message_document_title[^"]*"[^>]*>([^<]+)</i);
          const docSizeMatch = html.match(/class="tgme_widget_message_document_extra[^"]*"[^>]*>([^<]+)</i);
          if (docTitleMatch) {
            const docTitle = docTitleMatch[1].trim();
            const docSize = docSizeMatch ? docSizeMatch[1].trim() : '';
            throw new Error(
              `هذا رابط منشور تليجرام يحتوي على الملف (${docTitle}${docSize ? ` - ${docSize}` : ''}). تليجرام لا يسمح بتحميل مرفقات المستندات عبر روابط الويب؛ فقط افتح المنشور في تطبيق تليجرام واعمل له تحويل (Forward) مباشرة إلى البوت @${botInfo?.username || 'UMED_TD_bot'} ليتم رفعه فوراً إلى Google Drive!`
            );
          }

          const videoSrcMatch = html.match(/<video[^>]+src="([^"]+)"/i);
          if (videoSrcMatch && videoSrcMatch[1]) {
            return {
              resolvedUrl: videoSrcMatch[1],
              detectedFileName: `${channelUsername}_${messageId}.mp4`,
              detectedMimeType: 'video/mp4',
            };
          }

          const photoMatch = html.match(/tgme_widget_message_photo_wrap[^>]+background-image:url\('([^']+)'\)/i);
          if (photoMatch && photoMatch[1]) {
            return {
              resolvedUrl: photoMatch[1],
              detectedFileName: `${channelUsername}_${messageId}.jpg`,
              detectedMimeType: 'image/jpeg',
            };
          }
        }

        throw new Error(
          `هذا رابط منشور تليجرام (${channelUsername}/${messageId}) وليس رابط ملف مباشر. لرفع ملفات من قنوات أو مجموعات تليجرام، افتح الرسالة في تليجرام واعمل لها تحويل (Forward) إلى البوت @${botInfo?.username || 'UMED_TD_bot'}.`
        );
      }
    }

    return { resolvedUrl: rawUrl };
  } catch (err: any) {
    if (
      err?.message &&
      (err.message.includes('منشور تليجرام') ||
        err.message.includes('يوتيوب') ||
        err.message.includes('Video ID') ||
        err.message.includes('yt-dlp'))
    ) {
      throw err;
    }
    return { resolvedUrl: rawUrl };
  }
}

// ============================================================================
// File & Media Compression Engine (ZIP Archive & FFmpeg Video/Audio Shrinker)
// ============================================================================

async function compressLocalFile(
  inputPath: string,
  originalFileName: string,
  originalMimeType: string,
  compressMode: CompressMode,
  signal: AbortSignal
): Promise<{
  finalPath: string;
  finalFileName: string;
  finalMimeType: string;
  wasCompressed: boolean;
}> {
  if (!compressMode || compressMode === 'none') {
    return {
      finalPath: inputPath,
      finalFileName: originalFileName,
      finalMimeType: originalMimeType,
      wasCompressed: false,
    };
  }

  const lowerName = originalFileName.toLowerCase();
  const isVideo =
    originalMimeType.startsWith('video/') ||
    /\.(mp4|mkv|mov|webm|avi|flv)$/i.test(lowerName);
  const isAudio =
    originalMimeType.startsWith('audio/') ||
    /\.(mp3|m4a|wav|ogg|aac|flac)$/i.test(lowerName);

  // Mode 1: FFmpeg Media Compression (shrinks video/audio resolution & bitrate)
  if (compressMode === 'media' && (isVideo || isAudio)) {
    const ext = isAudio ? '.mp3' : '.mp4';
    const baseWithoutExt = originalFileName.replace(/\.[^/.]+$/, '');
    const outMediaPath = `${inputPath}_compressed${ext}`;
    try {
      if (isVideo) {
        await execFileAsync(
          'ffmpeg',
          [
            '-y',
            '-i',
            inputPath,
            '-vf',
            "scale='min(854,iw)':-2",
            '-c:v',
            'libx264',
            '-preset',
            'ultrafast',
            '-crf',
            '28',
            '-c:a',
            'aac',
            '-b:a',
            '96k',
            '-movflags',
            '+faststart',
            outMediaPath,
          ],
          { signal, timeout: 600000 }
        );
      } else {
        await execFileAsync(
          'ffmpeg',
          ['-y', '-i', inputPath, '-vn', '-c:a', 'libmp3lame', '-b:a', '96k', outMediaPath],
          { signal, timeout: 300000 }
        );
      }

      if (fs.existsSync(outMediaPath) && fs.statSync(outMediaPath).size > 0) {
        return {
          finalPath: outMediaPath,
          finalFileName: `${baseWithoutExt} (مضغوط)${ext}`,
          finalMimeType: isAudio ? 'audio/mpeg' : 'video/mp4',
          wasCompressed: true,
        };
      }
    } catch (err: any) {
      if (signal.aborted) throw new Error('CANCELLED_BY_USER');
      console.warn('FFmpeg media compression fallback to ZIP:', err?.message);
    }
  }

  // Mode 2: Standard ZIP Archive Compression (.zip)
  if (lowerName.endsWith('.zip')) {
    return {
      finalPath: inputPath,
      finalFileName: originalFileName,
      finalMimeType: 'application/zip',
      wasCompressed: false,
    };
  }

  const outZipPath = `${inputPath}.zip`;
  await execFileAsync(
    'python3',
    [
      '-c',
      'import zipfile, sys; z = zipfile.ZipFile(sys.argv[1], "w", zipfile.ZIP_DEFLATED, compresslevel=6); z.write(sys.argv[2], arcname=sys.argv[3]); z.close()',
      outZipPath,
      inputPath,
      originalFileName,
    ],
    { signal, timeout: 300000 }
  );

  if (fs.existsSync(outZipPath) && fs.statSync(outZipPath).size > 0) {
    return {
      finalPath: outZipPath,
      finalFileName: `${originalFileName}.zip`,
      finalMimeType: 'application/zip',
      wasCompressed: true,
    };
  }

  return {
    finalPath: inputPath,
    finalFileName: originalFileName,
    finalMimeType: originalMimeType,
    wasCompressed: false,
  };
}

// ============================================================================
// Core Turbo Streaming Pipeline (6x Independent MTProto Single-Wave 3MB Batch + 13.5ms Wall-Clock Deadline Paced IPv4 Drive Upload)
// ============================================================================

const DRIVE_CHUNK_SIZE = 3 * 1024 * 1024; // 3 MB (6 * 512 KB = 12 * 256 KB): exact 1-to-1 single wave on 6 MTProto clients + exact 256KB Drive multiple
const MTPROTO_PART_SIZE = 512 * 1024; // 512 KB (maximum allowed by Telegram GetFile)
const MTPROTO_BATCH_PARTS = 6; // 6 * 512 KB = 3 MB per single-wave batch (1 part per client)
const MTPROTO_PART_TIMEOUT_MS = 8500; // Strict timeout per 512KB request
const DRIVE_WRITE_SLICE_BYTES = 64 * 1024; // 64 KB slice for smooth token-bucket pacing
const DRIVE_WRITE_SLICE_DEADLINE_MS = 13.5; // Wall-clock deadline per 64KB slice (48 slices = ~648ms + RTT = ~735ms per 3MB)

const driveHttpsAgent = new https.Agent({
  keepAlive: true,
  family: 4,
  maxSockets: 4,
  keepAliveMsecs: 30000,
});

function withTimeout<T>(promise: Promise<T>, ms: number, label: string): Promise<T> {
  return new Promise<T>((resolve, reject) => {
    const timer = setTimeout(() => {
      reject(new Error(`TIMEOUT:${label}`));
    }, ms);
    promise.then(
      (val) => {
        clearTimeout(timer);
        resolve(val);
      },
      (err) => {
        clearTimeout(timer);
        reject(err);
      }
    );
  });
}

async function* createParallelMtprotoStream(
  primaryClient: TelegramClient,
  media: any,
  expectedTotalBytes: number,
  abortSignal: AbortSignal,
  startOffsetBytes: number = 0
): AsyncGenerator<Uint8Array> {
  const info = utils.getFileInfo(media);
  let targetDcId: number = info.dcId || primaryClient.session.dcId;
  const location = info.location;
  const fileSize: number =
    expectedTotalBytes > 0
      ? expectedTotalBytes
      : info.size
      ? Number(info.size.toString())
      : 0;

  if (!location || fileSize <= 0) {
    const fallback = primaryClient.iterDownload({
      file: media,
      requestSize: MTPROTO_PART_SIZE,
    });
    for await (const chunk of fallback as unknown as AsyncIterable<Uint8Array>) {
      if (abortSignal.aborted) throw new Error('CANCELLED_BY_USER');
      yield chunk;
    }
    return;
  }

  const totalParts = Math.ceil(fileSize / MTPROTO_PART_SIZE);
  const startPartIndex = Math.floor(Math.max(0, startOffsetBytes) / MTPROTO_PART_SIZE);
  const activeClients =
    mtprotoPoolClients.length > 0 ? [...mtprotoPoolClients] : [primaryClient];

  const fetchSinglePartOnce = async (
    workerClient: TelegramClient,
    partIndex: number
  ): Promise<Buffer> => {
    if (abortSignal.aborted) {
      throw new Error('CANCELLED_BY_USER');
    }
    if (!workerClient.connected) {
      await withTimeout(workerClient.connect(), 8000, 'connect');
    }
    const sender = await withTimeout(
      getSafeClientSender(workerClient, targetDcId),
      12000,
      'getSender'
    );
    preventExportedSenderAutoDisconnect(workerClient, targetDcId);

    const partOffset = bigInt(partIndex).multiply(MTPROTO_PART_SIZE);
    const res: any = await withTimeout(
      workerClient.invokeWithSender(
        new Api.upload.GetFile({
          location,
          offset: partOffset,
          limit: MTPROTO_PART_SIZE,
        }),
        sender
      ),
      MTPROTO_PART_TIMEOUT_MS,
      `GetFile_${partIndex}`
    );
    preventExportedSenderAutoDisconnect(workerClient, targetDcId);

    if (res && res.bytes) {
      return Buffer.from(res.bytes);
    }
    return Buffer.alloc(0);
  };

  // Download in non-overlapping 3 MB (6 x 512 KB) single-wave batches (1 part per client = ~205ms per 3MB)
  for (let basePart = startPartIndex; basePart < totalParts; basePart += MTPROTO_BATCH_PARTS) {
    if (abortSignal.aborted) {
      throw new Error('CANCELLED_BY_USER');
    }

    const countInBatch = Math.min(MTPROTO_BATCH_PARTS, totalParts - basePart);
    const partBuffers: Buffer[] = new Array(countInBatch);
    const idleClientsInBatch: TelegramClient[] = [];

    const downloadPartInWave = async (localIdx: number, globalPart: number): Promise<Buffer> => {
      let retries = 0;
      while (true) {
        if (abortSignal.aborted) throw new Error('CANCELLED_BY_USER');
        const assignedClient =
          activeClients[(localIdx + retries) % activeClients.length];

        let stragglerTimer: ReturnType<typeof setTimeout> | null = null;
        try {
          const primaryPromise = fetchSinglePartOnce(assignedClient, globalPart).then((buf) => {
            idleClientsInBatch.push(assignedClient);
            return buf;
          });

          // Only fire a backup request if at least 4 other clients in this wave have ALREADY finished and are idle!
          const stragglerGuard = new Promise<Buffer>((resolve, reject) => {
            stragglerTimer = setTimeout(() => {
              if (abortSignal.aborted) {
                reject(new Error('CANCELLED_BY_USER'));
                return;
              }
              const freeClient = idleClientsInBatch.pop();
              if (freeClient && freeClient !== assignedClient) {
                fetchSinglePartOnce(freeClient, globalPart).then(resolve, reject);
              }
            }, 380);
          });

          const buf = await Promise.race([primaryPromise, stragglerGuard]);
          if (stragglerTimer) clearTimeout(stragglerTimer);
          return buf;
        } catch (err: any) {
          if (stragglerTimer) clearTimeout(stragglerTimer);
          if (abortSignal.aborted) throw new Error('CANCELLED_BY_USER');

          if (err instanceof errors.FileMigrateError || err?.newDc) {
            targetDcId = err.newDc;
            continue;
          }

          if (err instanceof errors.FloodWaitError || err?.seconds) {
            const waitMs = Math.min(5000, (err.seconds || 1) * 1000);
            await new Promise((r) => setTimeout(r, waitMs));
            retries++;
            continue;
          }

          retries++;
          if (retries > 6) {
            throw err;
          }
          await new Promise((r) => setTimeout(r, 200 * retries));
        }
      }
    };

    await Promise.all(
      Array.from({ length: countInBatch }, async (_, localIdx) => {
        const globalPart = basePart + localIdx;
        partBuffers[localIdx] = await downloadPartInWave(localIdx, globalPart);
      })
    );

    const batchBuffer = Buffer.concat(partBuffers);
    if (batchBuffer.byteLength > 0) {
      yield batchBuffer;
    }
  }
}

async function uploadBufferToDrivePaced(
  sessionUri: string,
  bufferToSend: Buffer,
  headers: Record<string, string>,
  abortSignal: AbortSignal,
  onProgressBytes?: (writtenInChunk: number) => void
): Promise<{ status: number; headers: Record<string, any>; bodyText: string }> {
  return new Promise((resolve, reject) => {
    if (abortSignal.aborted) {
      reject(new Error('CANCELLED_BY_USER'));
      return;
    }

    let settled = false;
    const finishResolve = (val: {
      status: number;
      headers: Record<string, any>;
      bodyText: string;
    }) => {
      if (settled) return;
      settled = true;
      clearTimeout(timeoutHandle);
      abortSignal.removeEventListener('abort', onAbort);
      resolve(val);
    };
    const finishReject = (err: Error) => {
      if (settled) return;
      settled = true;
      clearTimeout(timeoutHandle);
      abortSignal.removeEventListener('abort', onAbort);
      reject(err);
    };

    const req = https.request(
      sessionUri,
      {
        method: 'PUT',
        agent: driveHttpsAgent,
        family: 4,
        headers,
      },
      (res) => {
        const resChunks: Buffer[] = [];
        res.on('data', (d) => resChunks.push(Buffer.from(d)));
        res.on('end', () => {
          finishResolve({
            status: res.statusCode || 0,
            headers: res.headers,
            bodyText: Buffer.concat(resChunks).toString('utf8'),
          });
        });
        res.on('error', finishReject);
      }
    );

    const onAbort = () => {
      req.destroy(new Error('CANCELLED_BY_USER'));
      finishReject(new Error('CANCELLED_BY_USER'));
    };
    abortSignal.addEventListener('abort', onAbort, { once: true });

    const timeoutHandle = setTimeout(() => {
      req.destroy(new Error('DRIVE_PUT_TIMEOUT'));
      finishReject(new Error('DRIVE_PUT_TIMEOUT'));
    }, 12000);

    req.on('error', finishReject);

    (async () => {
      try {
        if (bufferToSend.byteLength === 0) {
          req.end();
          return;
        }
        const paceStart = Date.now();
        let sliceIdx = 0;
        for (let off = 0; off < bufferToSend.byteLength; off += DRIVE_WRITE_SLICE_BYTES) {
          if (settled || abortSignal.aborted) return;
          const targetTime = paceStart + Math.round(sliceIdx * DRIVE_WRITE_SLICE_DEADLINE_MS);
          const waitMs = targetTime - Date.now();
          if (waitMs > 1) {
            await new Promise((r) => setTimeout(r, waitMs));
          }
          if (settled || abortSignal.aborted) return;

          const endOff = Math.min(off + DRIVE_WRITE_SLICE_BYTES, bufferToSend.byteLength);
          const slice = bufferToSend.subarray(off, endOff);
          const ok = req.write(slice);
          if (!ok && !settled) {
            await new Promise<void>((r) => req.once('drain', r));
          }
          if (onProgressBytes) {
            onProgressBytes(endOff);
          }
          sliceIdx++;
        }
        if (!settled) {
          req.end();
        }
      } catch (writeErr: any) {
        finishReject(writeErr instanceof Error ? writeErr : new Error(String(writeErr)));
      }
    })();
  });
}

async function queryResumableUploadOffset(
  sessionUri: string,
  totalBytes: number,
  abortSignal: AbortSignal
): Promise<number> {
  try {
    const res = await uploadBufferToDrivePaced(
      sessionUri,
      Buffer.alloc(0),
      {
        'Content-Length': '0',
        'Content-Range': `bytes */${totalBytes > 0 ? totalBytes : '*'}`,
      },
      abortSignal
    );
    if (res.status === 308 && res.headers.range) {
      const m = String(res.headers.range).match(/bytes=0-(\d+)/i);
      if (m && m[1]) {
        const receivedBytes = parseInt(m[1], 10) + 1;
        // Align down to DRIVE_CHUNK_SIZE (3 MB) boundary
        return Math.floor(receivedBytes / DRIVE_CHUNK_SIZE) * DRIVE_CHUNK_SIZE;
      }
    }
  } catch {
    // Ignore probe error and start from 0
  }
  return 0;
}

async function streamAsyncIterableToDrive(
  job: TransferJob,
  sessionUri: string,
  targetFolderName: string,
  chunkSource: AsyncIterable<Uint8Array>,
  abortSignal: AbortSignal,
  initialUploadedOffset: number = 0
): Promise<any> {
  const startTime = Date.now();
  let lastTelegramEditTime = 0;

  let pendingBuffer = Buffer.alloc(0);
  let uploadedOffset = initialUploadedOffset;
  job.bytesTransferred = initialUploadedOffset;

  const cancelKeyboard = {
    inline_keyboard: [[{ text: '⛔ إلغاء رفع هذا الملف', callback_data: `cancel_${job.id}` }]],
  };

  const updateProgressNotification = () => {
    const elapsedSec = Math.max(0.15, (Date.now() - startTime) / 1000);
    const bytesInThisSession = Math.max(0, job.bytesTransferred - initialUploadedOffset);
    job.speedBps = Math.round(bytesInThisSession / elapsedSec);

    const now = Date.now();
    // Update immediately on the very first progress update (lastTelegramEditTime === 0), then every 2s
    if (job.chatId && job.statusMessageId && (lastTelegramEditTime === 0 || now - lastTelegramEditTime > 2000)) {
      lastTelegramEditTime = now;
      const pct =
        job.totalBytes > 0
          ? Math.min(99, Math.round((job.bytesTransferred / job.totalBytes) * 100))
          : 0;
      const modeBadge =
        job.protocol === 'mtproto'
          ? `🚀 MTProto Turbo (${Math.max(1, mtprotoPoolClients.length)}x جلسات متوازية)`
          : '🔄 تدفق مباشر فائق السرعة';
      const progressText =
        `${modeBadge} — <b>جاري الرفع إلى Google Drive...</b>\n` +
        `📄 <b>الملف:</b> <code>${job.fileName}</code>\n` +
        `📦 <b>المنقول:</b> ${formatBytes(job.bytesTransferred)}${
          job.totalBytes > 0 ? ` / ${formatBytes(job.totalBytes)} (${pct}%)` : ''
        }\n` +
        `🚀 <b>السرعة:</b> ${formatBytes(job.speedBps)}/s\n` +
        `📁 <b>المجلد:</b> ${targetFolderName}`;
      editTelegramMessage(job.chatId, job.statusMessageId, progressText, cancelKeyboard);
    }
  };

  const uploadSingleDriveChunk = async (chunkToSend: Buffer, startByte: number) => {
    const endByte = startByte + DRIVE_CHUNK_SIZE - 1;
    let attempt = 0;

    while (true) {
      if (abortSignal.aborted) throw new Error('CANCELLED_BY_USER');
      try {
        const res = await uploadBufferToDrivePaced(
          sessionUri,
          chunkToSend,
          {
            'Content-Length': String(DRIVE_CHUNK_SIZE),
            'Content-Range': `bytes ${startByte}-${endByte}/*`,
          },
          abortSignal,
          (writtenInChunk) => {
            job.bytesTransferred = startByte + writtenInChunk;
            if (writtenInChunk % (512 * 1024) === 0 || writtenInChunk === DRIVE_CHUNK_SIZE) {
              updateProgressNotification();
            }
          }
        );

        if (res.status !== 308 && (res.status < 200 || res.status >= 300)) {
          if (res.status === 401 || res.status === 403) {
            driveSession.accessToken = null;
            job.status = 'waiting_auth';
            throw new Error('انتهت صلاحية جلسة Google Drive. يرجى تحديث الاتصال من لوحة التحكم.');
          }
          if (res.status >= 500 && attempt < 4) {
            attempt++;
            await new Promise((r) => setTimeout(r, 400 * attempt));
            continue;
          }
          throw new Error(`فشل رفع جزء من الملف إلى Google Drive (${res.status}): ${res.bodyText}`);
        }

        job.resumableUploadedOffset = startByte + DRIVE_CHUNK_SIZE;
        if (job.resumableUploadedOffset % (12 * 1024 * 1024) === 0) {
          saveStateToDisk();
        }
        return;
      } catch (err: any) {
        if (abortSignal.aborted || err?.message === 'CANCELLED_BY_USER') {
          throw new Error('CANCELLED_BY_USER');
        }
        attempt++;
        if (attempt > 4 || job.status === 'waiting_auth') {
          throw err;
        }
        await new Promise((r) => setTimeout(r, 400 * attempt));
      }
    }
  };

  for await (const rawChunk of chunkSource) {
    if (abortSignal.aborted || (job.status as string) === 'cancelled') {
      throw new Error('CANCELLED_BY_USER');
    }

    if (rawChunk && rawChunk.byteLength > 0) {
      pendingBuffer = Buffer.concat([pendingBuffer, Buffer.from(rawChunk)]);
      if (uploadedOffset === initialUploadedOffset && job.bytesTransferred === initialUploadedOffset) {
        job.bytesTransferred = initialUploadedOffset + Math.min(pendingBuffer.byteLength, 512 * 1024);
        updateProgressNotification();
      }
    }

    // Sequentially upload each 3MB single-wave batch so Telegram ingress and Drive egress never collide
    while (pendingBuffer.byteLength >= DRIVE_CHUNK_SIZE) {
      if (abortSignal.aborted || (job.status as string) === 'cancelled') {
        throw new Error('CANCELLED_BY_USER');
      }

      const chunkToSend = Buffer.from(pendingBuffer.subarray(0, DRIVE_CHUNK_SIZE));
      pendingBuffer = pendingBuffer.subarray(DRIVE_CHUNK_SIZE);
      const startByte = uploadedOffset;
      uploadedOffset += DRIVE_CHUNK_SIZE;

      await uploadSingleDriveChunk(chunkToSend, startByte);
    }
  }

  if (abortSignal.aborted || (job.status as string) === 'cancelled') {
    throw new Error('CANCELLED_BY_USER');
  }

  const remainingBytes = pendingBuffer.byteLength;
  const exactTotalSize = uploadedOffset + remainingBytes;
  job.totalBytes = exactTotalSize;

  const finalHeaders: Record<string, string> = {
    'Content-Type': job.mimeType || 'application/octet-stream',
    'Content-Length': String(remainingBytes),
  };

  if (uploadedOffset > 0 && exactTotalSize > 0) {
    finalHeaders['Content-Range'] =
      remainingBytes > 0
        ? `bytes ${uploadedOffset}-${exactTotalSize - 1}/${exactTotalSize}`
        : `bytes */${exactTotalSize}`;
  }

  let finalAttempt = 0;
  while (true) {
    if (abortSignal.aborted) throw new Error('CANCELLED_BY_USER');
    try {
      const finalRes = await uploadBufferToDrivePaced(
        sessionUri,
        pendingBuffer,
        finalHeaders,
        abortSignal,
        (writtenInChunk) => {
          job.bytesTransferred = uploadedOffset + writtenInChunk;
          if (writtenInChunk % (512 * 1024) === 0 || writtenInChunk === remainingBytes) {
            updateProgressNotification();
          }
        }
      );

      if (finalRes.status < 200 || finalRes.status >= 300) {
        if (finalRes.status === 401 || finalRes.status === 403) {
          driveSession.accessToken = null;
          job.status = 'waiting_auth';
          throw new Error('انتهت صلاحية جلسة Google Drive. يرجى تحديث الاتصال من لوحة التحكم.');
        }
        if (finalRes.status >= 500 && finalAttempt < 3) {
          finalAttempt++;
          await new Promise((r) => setTimeout(r, 600 * finalAttempt));
          continue;
        }
        throw new Error(
          `فشل إتمام رفع الملف إلى Google Drive (${finalRes.status}): ${finalRes.bodyText}`
        );
      }

      job.bytesTransferred = exactTotalSize;
      job.resumableSessionUri = undefined;
      job.resumableUploadedOffset = undefined;
      return JSON.parse(finalRes.bodyText);
    } catch (err: any) {
      if (abortSignal.aborted || err?.message === 'CANCELLED_BY_USER') {
        throw new Error('CANCELLED_BY_USER');
      }
      finalAttempt++;
      if (finalAttempt > 3 || job.status === 'waiting_auth') {
        throw err;
      }
      await new Promise((r) => setTimeout(r, 600 * finalAttempt));
    }
  }
}

async function* readableStreamToAsyncIterable(stream: ReadableStream<Uint8Array>): AsyncGenerator<Uint8Array> {
  const reader = stream.getReader();
  try {
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      if (value) yield value;
    }
  } finally {
    reader.releaseLock();
  }
}

async function saveAsyncIterableToTempFileWithProgress(
  job: TransferJob,
  chunkSource: AsyncIterable<Uint8Array>,
  tempFilePath: string,
  signal: AbortSignal
): Promise<void> {
  const writeStream = fs.createWriteStream(tempFilePath);
  const startTime = Date.now();
  let lastEdit = 0;
  const cancelKeyboard = {
    inline_keyboard: [[{ text: '⛔ إلغاء العملية', callback_data: `cancel_${job.id}` }]],
  };

  for await (const chunk of chunkSource) {
    if (signal.aborted || (job.status as string) === 'cancelled') {
      writeStream.destroy();
      throw new Error('CANCELLED_BY_USER');
    }
    if (chunk && chunk.byteLength > 0) {
      const canContinue = writeStream.write(Buffer.from(chunk));
      if (!canContinue) {
        await new Promise<void>((resolve) => writeStream.once('drain', resolve));
      }
      job.bytesTransferred += chunk.byteLength;
      const elapsedSec = Math.max(0.2, (Date.now() - startTime) / 1000);
      job.speedBps = Math.round(job.bytesTransferred / elapsedSec);

      const now = Date.now();
      if (job.chatId && job.statusMessageId && now - lastEdit > 2800) {
        lastEdit = now;
        const pct =
          job.totalBytes > 0 ? Math.min(99, Math.round((job.bytesTransferred / job.totalBytes) * 100)) : 0;
        await editTelegramMessage(
          job.chatId,
          job.statusMessageId,
          `📥 <b>جاري سحب الملف لتحضيره وضغطه...</b>\n` +
            `📄 <b>الملف:</b> <code>${job.fileName}</code>\n` +
            `📦 <b>المسحوب:</b> ${formatBytes(job.bytesTransferred)}${
              job.totalBytes > 0 ? ` / ${formatBytes(job.totalBytes)} (${pct}%)` : ''
            }\n` +
            `🚀 <b>السرعة:</b> ${formatBytes(job.speedBps)}/s`,
          cancelKeyboard
        );
      }
    }
  }

  await new Promise<void>((resolve, reject) => {
    writeStream.end((err?: Error | null) => (err ? reject(err) : resolve()));
  });
}

function resolveJobDriveSession(job: TransferJob): {
  accessToken: string | null;
  userEmail: string | null;
  userName: string | null;
  activeFolderId: string | null;
  activeFolderName: string;
  accountEnabled: boolean;
  autoCategorizeByType: boolean;
  skipDuplicates: boolean;
  urlHandlingMode: 'ask' | 'to_drive' | 'to_telegram';
  defaultQuality: string;
  defaultCompressMode: CompressMode;
  profile: UserDriveProfile;
} {
  if (job.accountEmail && job.accountEmail !== 'default' && userProfiles[job.accountEmail]) {
    const prof = userProfiles[job.accountEmail];
    return {
      accessToken: prof.accessToken,
      userEmail: prof.userEmail,
      userName: prof.userName,
      activeFolderId: prof.activeFolderId,
      activeFolderName: prof.activeFolderName || 'Telegram Bot Uploads',
      accountEnabled: prof.accountEnabled,
      autoCategorizeByType: prof.autoCategorizeByType,
      skipDuplicates: prof.skipDuplicates,
      urlHandlingMode: prof.urlHandlingMode,
      defaultQuality: prof.defaultQuality || '720',
      defaultCompressMode: prof.defaultCompressMode || 'none',
      profile: prof,
    };
  }
  return getEffectiveSessionForChat(job.chatId);
}

async function executeTransferJob(job: TransferJob): Promise<void> {
  if (job.status === 'cancelled') return;

  const userSess = resolveJobDriveSession(job);
  if (!userSess.accessToken || !userSess.accountEnabled) {
    job.status = 'waiting_auth';
    saveStateToDisk();
    return;
  }

  const token = userSess.accessToken;
  job.accountEmail = userSess.userEmail || job.accountEmail || 'default';

  const abortController = new AbortController();
  jobAbortControllers.set(job.id, abortController);
  const { signal } = abortController;

  const tempFilesToClean: string[] = [];

  try {
    job.status = 'downloading';
    job.errorMessage = undefined;
    job.bytesTransferred = 0;
    job.speedBps = 0;

    const effectiveCompressMode: CompressMode =
      job.compressMode || userSess.defaultCompressMode || 'none';
    job.compressMode = effectiveCompressMode;

    let targetFolderId = userSess.activeFolderId;
    let targetFolderName = userSess.activeFolderName || 'Telegram Bot Uploads';

    if (!targetFolderId) {
      const folder = await ensureDriveFolder(token, targetFolderName);
      userSess.profile.activeFolderId = folder.id;
      userSess.profile.activeFolderName = folder.name;
      if (!job.chatId || job.chatId === adminConfig.ownerChatId) {
        driveSession.activeFolderId = folder.id;
        driveSession.activeFolderName = folder.name;
      }
      targetFolderId = folder.id;
      targetFolderName = folder.name;
    }

    if (userSess.autoCategorizeByType && targetFolderId) {
      const subName = getSubfolderNameForMime(
        effectiveCompressMode === 'zip' ? 'application/zip' : job.mimeType
      );
      const subFolder = await ensureDriveFolder(token, subName, targetFolderId);
      targetFolderId = subFolder.id;
      targetFolderName = `${userSess.profile.activeFolderName || 'Telegram Bot Uploads'} / ${subFolder.name}`;
    }

    job.folderId = targetFolderId || undefined;
    job.folderName = targetFolderName;

    // Check for duplicate file in the user's personal Google Drive account & folder BEFORE downloading/uploading
    if (effectiveCompressMode === 'none') {
      const existingDuplicate = await findExistingDuplicateForAccount(
        job,
        token,
        targetFolderId,
        userSess.skipDuplicates
      );
      if (existingDuplicate) {
        job.status = 'completed';
        job.isDuplicateSkipped = true;
        job.driveFileId = existingDuplicate.id;
        job.webViewLink = existingDuplicate.webViewLink;
        if (existingDuplicate.size && !job.totalBytes) {
          job.totalBytes = existingDuplicate.size;
        }
        job.bytesTransferred = job.totalBytes;
        job.completedAt = new Date().toISOString();
        jobAbortControllers.delete(job.id);
        saveStateToDisk();

        if (job.chatId && job.statusMessageId) {
          const dupText =
            `⚡ <b>تم تخطي الرفع (الملف موجود مسبقاً في حسابك بدون تكرار!)</b>\n\n` +
            `📄 <b>الاسم:</b> <code>${job.fileName}</code>\n` +
            `📦 <b>الحجم:</b> ${formatBytes(job.totalBytes)}\n` +
            `📁 <b>المجلد:</b> ${targetFolderName}\n` +
            `🔗 <a href="${job.webViewLink}">فتح الملف الموجود في Google Drive</a>`;
          const dupKeyboard = job.webViewLink
            ? {
                inline_keyboard: [
                  [
                    { text: '🔗 فتح الملف في Google Drive', url: job.webViewLink },
                    { text: '⚙️ الإعدادات', callback_data: 'open_settings' },
                  ],
                ],
              }
            : undefined;
          await editTelegramMessage(job.chatId, job.statusMessageId, dupText, dupKeyboard);
        }
        return;
      }
    }

    if (signal.aborted || (job.status as string) === 'cancelled') {
      throw new Error('CANCELLED_BY_USER');
    }

    let resumeOffset = 0;
    let activeSessionUri = job.resumableSessionUri || '';
    if (activeSessionUri && effectiveCompressMode === 'none' && job.source === 'telegram') {
      resumeOffset = await queryResumableUploadOffset(activeSessionUri, job.totalBytes, signal);
      if (resumeOffset === 0) {
        activeSessionUri = '';
        job.resumableSessionUri = undefined;
        job.resumableUploadedOffset = undefined;
      }
    }

    let sourceAsyncStream: AsyncIterable<Uint8Array>;

    if (job.source === 'telegram' && job.telegramFileId) {
      const isOverStandardLimit = job.totalBytes > 19.5 * 1024 * 1024;
      let useMtproto = isOverStandardLimit && mtprotoConnected;
      let downloadUrl = '';

      if (!useMtproto) {
        try {
          const fileInfo = await telegramApi<{ file_id: string; file_size?: number; file_path?: string }>(
            'getFile',
            { file_id: job.telegramFileId },
            signal
          );
          if (!fileInfo.file_path) {
            throw new Error('لم يتم العثور على مسار الملف من خادم تليجرام.');
          }
          if (fileInfo.file_size && !job.totalBytes) {
            job.totalBytes = fileInfo.file_size;
          }
          downloadUrl = `${getTelegramApiRoot()}/file/bot${getBotToken()}/${fileInfo.file_path}`;
          job.protocol = 'bot_api';
        } catch (err: any) {
          if (signal.aborted) throw new Error('CANCELLED_BY_USER');
          const msg = err?.message || '';
          if (msg.toLowerCase().includes('file is too big')) {
            if (mtprotoConnected && mtprotoClient) {
              useMtproto = true;
            } else {
              throw new Error('حجم الملف أكبر من 20MB ومحرك MTProto غير متصل حالياً.');
            }
          } else {
            throw err;
          }
        }
      }

      if (useMtproto && mtprotoClient) {
        job.protocol = 'mtproto';
        const mtMsg = await getMtprotoMessageForJob(job);
        if (!mtMsg || !mtMsg.media) {
          throw new Error(
            'تعذر جلب بيانات الملف الضخم عبر MTProto. يرجى إعادة إرسال أو تحويل (Forward) الملف للبوت مرة أخرى.'
          );
        }
        sourceAsyncStream = createParallelMtprotoStream(
          mtprotoClient,
          mtMsg.media,
          job.totalBytes,
          signal,
          resumeOffset
        );
      } else {
        resumeOffset = 0;
        activeSessionUri = '';
        const sourceRes = await fetch(downloadUrl, { signal });
        if (!sourceRes.ok || !sourceRes.body) {
          throw new Error(`فشل الاتصال بخادم ملفات تليجرام (${sourceRes.status})`);
        }
        sourceAsyncStream = readableStreamToAsyncIterable(sourceRes.body);
      }
    } else if (job.directUrl) {
      resumeOffset = 0;
      activeSessionUri = '';
      job.protocol = 'http';
      const resolved = await resolveTelegramPostLinkIfApplicable(
        job.directUrl,
        job.mediaFormat || 'video',
        job.quality || userSess.defaultQuality
      );
      const downloadUrl = resolved.resolvedUrl;
      if (
        resolved.detectedFileName &&
        (job.fileName.startsWith('file_') ||
          job.fileName.endsWith('.bin') ||
          job.fileName.startsWith('YouTube_') ||
          job.fileName.startsWith('TikTok_') ||
          job.fileName.startsWith('Video_'))
      ) {
        job.fileName = resolved.detectedFileName;
      }
      if (resolved.detectedMimeType) {
        job.mimeType = resolved.detectedMimeType;
      }

      const sourceRes = await fetch(downloadUrl, {
        signal,
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
          ...(resolved.customHeaders || {}),
        },
      });
      if (!sourceRes.ok || !sourceRes.body) {
        throw new Error(`فشل الاتصال بمصدر الرابط (${sourceRes.status} ${sourceRes.statusText})`);
      }

      const contentLengthHeader = sourceRes.headers.get('content-length');
      const contentEncodingHeader = sourceRes.headers.get('content-encoding');
      if (contentLengthHeader && !contentEncodingHeader && (!job.totalBytes || job.totalBytes === 0)) {
        const parsedLength = parseInt(contentLengthHeader, 10);
        if (!isNaN(parsedLength) && parsedLength > 0) {
          job.totalBytes = parsedLength;
        }
      }

      const contentTypeHeader = sourceRes.headers.get('content-type');
      if (
        contentTypeHeader &&
        contentTypeHeader.toLowerCase().includes('text/html') &&
        !job.fileName.toLowerCase().endsWith('.html')
      ) {
        throw new Error('المصدر أعاد صفحة ويب (HTML) بدلاً من ملف الفيديو/الصوت المباشر. تأكد من صلاحية الرابط.');
      }
      if (contentTypeHeader && job.mimeType === 'application/octet-stream') {
        job.mimeType = contentTypeHeader.split(';')[0].trim();
      }

      const contentDisposition = sourceRes.headers.get('content-disposition');
      if (contentDisposition && (job.fileName.startsWith('file_') || job.fileName.endsWith('.bin'))) {
        const fileNameMatch = contentDisposition.match(/filename\*?=(?:UTF-8'')?["']?([^"';\n]+)["']?/i);
        if (fileNameMatch && fileNameMatch[1]) {
          try {
            job.fileName = decodeURIComponent(fileNameMatch[1].trim());
          } catch {
            job.fileName = fileNameMatch[1].trim();
          }
        }
      }

      if (effectiveCompressMode === 'none') {
        const urlDup = await findExistingDuplicateForAccount(
          job,
          token,
          targetFolderId,
          userSess.skipDuplicates
        );
        if (urlDup) {
          job.status = 'completed';
          job.isDuplicateSkipped = true;
          job.driveFileId = urlDup.id;
          job.webViewLink = urlDup.webViewLink;
          job.totalBytes = urlDup.size || job.totalBytes;
          job.bytesTransferred = job.totalBytes;
          job.completedAt = new Date().toISOString();
          jobAbortControllers.delete(job.id);
          saveStateToDisk();
          return;
        }
      }

      sourceAsyncStream = readableStreamToAsyncIterable(sourceRes.body);
    } else {
      throw new Error('لا يوجد مصدر صالح لتحميل الملف.');
    }

    // Optional Compression Step Before Uploading to Google Drive
    if (effectiveCompressMode !== 'none') {
      resumeOffset = 0;
      activeSessionUri = '';
      const safeTmpName = job.fileName.replace(/[^a-zA-Z0-9._\u0600-\u06FF-]/g, '_');
      const rawTempPath = path.join('/tmp', `drv_raw_${job.id}_${safeTmpName}`);
      tempFilesToClean.push(rawTempPath);

      await saveAsyncIterableToTempFileWithProgress(job, sourceAsyncStream, rawTempPath, signal);

      if (job.chatId && job.statusMessageId) {
        await editTelegramMessage(
          job.chatId,
          job.statusMessageId,
          `📦 <b>جاري ضغط الملف قبل الرفع إلى Google Drive (${formatCompressModeAr(effectiveCompressMode)})...</b>\n` +
            `📄 <b>الملف:</b> <code>${job.fileName}</code>`,
          {
            inline_keyboard: [[{ text: '⛔ إلغاء العملية', callback_data: `cancel_${job.id}` }]],
          }
        );
      }

      const compResult = await compressLocalFile(
        rawTempPath,
        job.fileName,
        job.mimeType,
        effectiveCompressMode,
        signal
      );

      if (compResult.finalPath !== rawTempPath) {
        tempFilesToClean.push(compResult.finalPath);
      }

      job.fileName = compResult.finalFileName;
      job.mimeType = compResult.finalMimeType;
      const compStat = fs.statSync(compResult.finalPath);
      job.totalBytes = compStat.size;
      job.bytesTransferred = 0;

      sourceAsyncStream = fs.createReadStream(compResult.finalPath, {
        highWaterMark: 4 * 1024 * 1024,
      }) as unknown as AsyncIterable<Uint8Array>;
    }

    job.status = 'uploading';
    const sessionUri =
      activeSessionUri ||
      (await createResumableUploadSession(
        token,
        job.fileName,
        job.mimeType,
        targetFolderId,
        `تم التحويل عبر بوت تليجرام من المرسل: ${job.senderName}`,
        signal
      ));
    job.resumableSessionUri = sessionUri;
    saveStateToDisk();

    const finalDriveFile = await streamAsyncIterableToDrive(
      job,
      sessionUri,
      targetFolderName,
      sourceAsyncStream,
      signal,
      resumeOffset
    );

    jobAbortControllers.delete(job.id);
    job.status = 'completed';
    job.driveFileId = finalDriveFile?.id;
    job.webViewLink =
      finalDriveFile?.webViewLink ||
      (finalDriveFile?.id ? `https://drive.google.com/file/d/${finalDriveFile.id}/view` : undefined);
    job.completedAt = new Date().toISOString();
    saveStateToDisk();

    if (job.chatId && job.statusMessageId) {
      const doneText =
        `✅ <b>تم رفع الملف بنجاح إلى Google Drive!</b>\n\n` +
        `📄 <b>الاسم:</b> <code>${job.fileName}</code>\n` +
        `📦 <b>الحجم:</b> ${formatBytes(job.bytesTransferred || job.totalBytes)}\n` +
        `📁 <b>المجلد:</b> ${targetFolderName}\n` +
        `🔗 <a href="${job.webViewLink}">فتح الملف في Google Drive</a>`;
      const doneRows: any[][] = [];
      if (job.webViewLink) {
        doneRows.push([{ text: '🔗 فتح الملف في Google Drive', url: job.webViewLink }]);
      }
      const baseAppUrl = (process.env.APP_URL || '').replace(/\/+$/, '');
      if (job.driveFileId && baseAppUrl && baseAppUrl.startsWith('https://')) {
        doneRows.push([
          {
            text: '📥 تحميل مباشر للجهاز',
            url: `${baseAppUrl}/api/direct-download?driveFileId=${encodeURIComponent(
              job.driveFileId
            )}&chatId=${encodeURIComponent(String(job.chatId))}`,
          },
        ]);
      }
      if (job.driveFileId) {
        doneRows.push([
          { text: '📲 سحب/إرسال نسخة إلى تليجرام', callback_data: `pull_drive_${job.driveFileId}` },
          { text: '🏠 القائمة الرئيسية', callback_data: 'open_main' },
        ]);
      } else {
        doneRows.push([{ text: '🏠 القائمة الرئيسية', callback_data: 'open_main' }]);
      }
      await editTelegramMessage(
        job.chatId,
        job.statusMessageId,
        doneText,
        doneRows.length > 0 ? { inline_keyboard: doneRows } : undefined
      );
    }
  } catch (error: any) {
    jobAbortControllers.delete(job.id);

    const rawMsg = error?.cause?.message || error?.message || 'حدث خطأ غير متوقع أثناء رفع الملف.';
    if (rawMsg === 'CANCELLED_BY_USER' || signal.aborted || (job.status as string) === 'cancelled') {
      job.status = 'cancelled';
      job.speedBps = 0;
      job.errorMessage = 'تم إلغاء رفع الملف بناءً على طلب المستخدم.';
      saveStateToDisk();
      return;
    }

    if (job.status !== 'waiting_auth') {
      job.status = 'failed';
    }
    job.errorMessage = rawMsg;
    saveStateToDisk();
    console.warn(`Transfer job ${job.id} did not complete: ${rawMsg}`);

    if (job.chatId && job.statusMessageId) {
      const failText =
        `❌ <b>تعذر إكمال العملية</b>\n\n` +
        `📄 <b>الملف:</b> <code>${job.fileName}</code>\n` +
        `⚠️ <b>السبب:</b> ${job.errorMessage}`;
      const retryKeyboard = {
        inline_keyboard: [
          [
            { text: '🔄 إعادة المحاولة', callback_data: `retry_${job.id}` },
            { text: '🗑️ حذف الملف الفاشل', callback_data: `delete_${job.id}` },
          ],
          [{ text: '🏠 القائمة الرئيسية', callback_data: 'open_main' }],
        ],
      };
      await editTelegramMessage(job.chatId, job.statusMessageId, failText, retryKeyboard);
    }
  } finally {
    for (const f of tempFilesToClean) {
      if (f && fs.existsSync(f)) {
        try {
          fs.unlinkSync(f);
        } catch {
          // Ignore cleanup error
        }
      }
    }
  }
}

// ============================================================================
// Pull File from Google Drive or External URL -> Send Directly to Telegram
// ============================================================================

async function listDriveFilesForTelegram(
  token: string,
  searchQuery?: string
): Promise<{ id: string; name: string; mimeType: string; size?: string; webViewLink?: string }[]> {
  let q = "mimeType != 'application/vnd.google-apps.folder' and trashed = false";
  if (searchQuery && searchQuery.trim()) {
    const escaped = searchQuery.trim().replace(/\\/g, '\\\\').replace(/'/g, "\\'");
    q += ` and name contains '${escaped}'`;
  }
  const orderBy = encodeURIComponent('createdTime desc');
  const res = await fetch(
    `https://www.googleapis.com/drive/v3/files?q=${encodeURIComponent(
      q
    )}&pageSize=12&orderBy=${orderBy}&fields=files(id,name,mimeType,size,webViewLink)`,
    {
      headers: { Authorization: `Bearer ${token}` },
    }
  );
  if (!res.ok) {
    if (res.status === 401 || res.status === 403) {
      throw new Error('انتهت صلاحية جلسة Google Drive. يرجى تنشيطها من لوحة التحكم.');
    }
    throw new Error('تعذر جلب قائمة الملفات من Google Drive.');
  }
  const data = await res.json();
  return data.files || [];
}

async function sendLocalFileToTelegramChat(
  chatId: number,
  tempFilePath: string,
  fileName: string,
  fileSize: number,
  caption: string,
  signal: AbortSignal,
  onUploadProgress?: (pct: number) => void
): Promise<void> {
  const token = getBotToken();
  if (!token) {
    throw new Error('TELEGRAM_BOT_TOKEN غير متوفر.');
  }

  // Use standard Bot API sendVideo / sendAudio / sendDocument for files <= 45 MB (fast & zero overhead)
  const MAX_BOT_API_SEND = 45 * 1024 * 1024;
  if (fileSize <= MAX_BOT_API_SEND && typeof fs.openAsBlob === 'function') {
    try {
      const blob = await fs.openAsBlob(tempFilePath);
      const lowerName = fileName.toLowerCase();
      const isMp4 = lowerName.endsWith('.mp4');
      const isMp3 = lowerName.endsWith('.mp3') || lowerName.endsWith('.m4a');

      const formData = new FormData();
      formData.append('chat_id', String(chatId));
      formData.append('caption', caption);
      formData.append('parse_mode', 'HTML');

      let endpoint = 'sendDocument';
      if (isMp4) {
        endpoint = 'sendVideo';
        formData.append('supports_streaming', 'true');
        formData.append('video', blob, fileName);
      } else if (isMp3) {
        endpoint = 'sendAudio';
        formData.append('audio', blob, fileName);
      } else {
        formData.append('document', blob, fileName);
      }

      const res = await fetch(`${getTelegramApiRoot()}/bot${token}/${endpoint}`, {
        method: 'POST',
        body: formData,
        signal,
      });
      const data = await res.json();
      if (data.ok) {
        return;
      }
      console.warn(`Bot API ${endpoint} fallback to MTProto:`, data.description);
    } catch (err: any) {
      if (signal.aborted) throw new Error('CANCELLED_BY_USER');
      console.warn('Bot API send error, falling back to MTProto:', err?.message);
    }
  }

  // Use MTProto 2GB Engine for large files (up to 2,000 MB) or as fallback
  if (!mtprotoClient || !mtprotoConnected) {
    await startMtprotoEngine();
  }
  if (!mtprotoClient || !mtprotoConnected) {
    throw new Error(
      fileSize > MAX_BOT_API_SEND
        ? 'حجم الملف أكبر من 50MB ومحرك MTProto (2GB) غير متصل حالياً.'
        : 'تعذر إرسال الملف إلى تليجرام.'
    );
  }

  if (!mtprotoClient.connected) {
    await mtprotoClient.connect();
  }

  const customFile = new CustomFile(fileName, fileSize, tempFilePath);
  await mtprotoClient.sendFile(chatId, {
    file: customFile,
    caption,
    forceDocument: !fileName.toLowerCase().endsWith('.mp4'),
    workers: 8,
    progressCallback: (progress: number) => {
      if (signal.aborted) {
        throw new Error('CANCELLED_BY_USER');
      }
      if (onUploadProgress) {
        onUploadProgress(Math.round(progress * 100));
      }
    },
  });
}

async function executePullToTelegramJob(job: TransferJob): Promise<void> {
  if ((job.status as string) === 'cancelled') return;

  const userSess = resolveJobDriveSession(job);
  const targetChatId = job.chatId || userSess.profile.chatId || adminConfig.ownerChatId;
  if (!targetChatId) {
    job.status = 'failed';
    job.errorMessage = 'لا يوجد معرف محادثة تليجرام (Chat ID). يرجى ربط حساب تليجرام أو إرسال /start للبوت أولاً.';
    saveStateToDisk();
    return;
  }
  job.chatId = targetChatId;

  const abortController = new AbortController();
  jobAbortControllers.set(job.id, abortController);
  const { signal } = abortController;

  const tempFilesToClean: string[] = [];

  try {
    job.status = 'downloading';
    job.direction = 'to_telegram';
    job.bytesTransferred = 0;
    job.speedBps = 0;
    const effectiveCompressMode: CompressMode =
      job.compressMode || userSess.defaultCompressMode || 'none';
    job.compressMode = effectiveCompressMode;
    saveStateToDisk();

    const cancelKeyboard = {
      inline_keyboard: [[{ text: '⛔ إلغاء سحب وإرسال هذا الملف', callback_data: `cancel_${job.id}` }]],
    };

    let responseStream: ReadableStream<Uint8Array> | null = null;

    if (job.source === 'drive_to_telegram' && job.driveFileId) {
      if (!userSess.accessToken) {
        job.status = 'waiting_auth';
        saveStateToDisk();
        throw new Error('يرجى ربط أو تنشيط جلسة Google Drive أولاً.');
      }

      const token = userSess.accessToken;
      const metaRes = await fetch(
        `https://www.googleapis.com/drive/v3/files/${job.driveFileId}?fields=id,name,mimeType,size,webViewLink`,
        {
          headers: { Authorization: `Bearer ${token}` },
          signal,
        }
      );
      if (!metaRes.ok) {
        if (metaRes.status === 401 || metaRes.status === 403) {
          userSess.profile.accessToken = null;
          job.status = 'waiting_auth';
          throw new Error('انتهت صلاحية جلسة Google Drive. يرجى تنشيطها من الموقع.');
        }
        throw new Error(`تعذر قراءة بيانات الملف من Google Drive (${metaRes.status})`);
      }

      const meta = await metaRes.json();
      job.fileName = meta.name || job.fileName || `drive_${job.driveFileId}`;
      job.mimeType = meta.mimeType || job.mimeType || 'application/octet-stream';
      if (meta.size) {
        job.totalBytes = parseInt(meta.size, 10) || job.totalBytes;
      }
      job.webViewLink = meta.webViewLink;

      let mediaUrl = `https://www.googleapis.com/drive/v3/files/${job.driveFileId}?alt=media`;
      if (job.mimeType.startsWith('application/vnd.google-apps.')) {
        mediaUrl = `https://www.googleapis.com/drive/v3/files/${job.driveFileId}/export?mimeType=application/pdf`;
        if (!job.fileName.toLowerCase().endsWith('.pdf')) {
          job.fileName += '.pdf';
        }
        job.mimeType = 'application/pdf';
      }

      const downloadRes = await fetch(mediaUrl, {
        headers: { Authorization: `Bearer ${token}` },
        signal,
      });

      if (!downloadRes.ok || !downloadRes.body) {
        throw new Error(`فشل سحب الملف من Google Drive (${downloadRes.status})`);
      }
      responseStream = downloadRes.body;
    } else if (job.directUrl) {
      const resolved = await resolveTelegramPostLinkIfApplicable(
        job.directUrl,
        job.mediaFormat || 'video',
        job.quality || userSess.defaultQuality
      );
      const downloadUrl = resolved.resolvedUrl;
      if (
        resolved.detectedFileName &&
        (job.fileName.startsWith('file_') ||
          job.fileName.endsWith('.bin') ||
          job.fileName.startsWith('YouTube_') ||
          job.fileName.startsWith('TikTok_') ||
          job.fileName.startsWith('Video_'))
      ) {
        job.fileName = resolved.detectedFileName;
      }
      if (resolved.detectedMimeType) {
        job.mimeType = resolved.detectedMimeType;
      }

      const sourceRes = await fetch(downloadUrl, {
        signal,
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
          ...(resolved.customHeaders || {}),
        },
      });

      if (!sourceRes.ok || !sourceRes.body) {
        throw new Error(`فشل الاتصال بمصدر الرابط (${sourceRes.status} ${sourceRes.statusText})`);
      }

      const contentTypeHeader = sourceRes.headers.get('content-type');
      if (
        contentTypeHeader &&
        contentTypeHeader.toLowerCase().includes('text/html') &&
        !job.fileName.toLowerCase().endsWith('.html')
      ) {
        throw new Error('المصدر أعاد صفحة ويب (HTML) بدلاً من ملف الفيديو/الصوت المباشر. تأكد من صلاحية الرابط.');
      }

      const contentLengthHeader = sourceRes.headers.get('content-length');
      const contentEncodingHeader = sourceRes.headers.get('content-encoding');
      if (contentLengthHeader && !contentEncodingHeader && (!job.totalBytes || job.totalBytes === 0)) {
        const parsedLen = parseInt(contentLengthHeader, 10);
        if (!isNaN(parsedLen) && parsedLen > 0) {
          job.totalBytes = parsedLen;
        }
      }

      const contentDisposition = sourceRes.headers.get('content-disposition');
      if (contentDisposition && (job.fileName.startsWith('file_') || job.fileName.endsWith('.bin'))) {
        const fileNameMatch = contentDisposition.match(/filename\*?=(?:UTF-8'')?["']?([^"';\n]+)["']?/i);
        if (fileNameMatch && fileNameMatch[1]) {
          try {
            job.fileName = decodeURIComponent(fileNameMatch[1].trim());
          } catch {
            job.fileName = fileNameMatch[1].trim();
          }
        }
      }

      responseStream = sourceRes.body;
    } else {
      throw new Error('لا يوجد مصدر صالح لسحب الملف إلى تليجرام.');
    }

    const safeFileName = job.fileName.replace(/[^a-zA-Z0-9._\u0600-\u06FF-]/g, '_');
    const rawTempFilePath = path.join('/tmp', `tg_pull_${job.id}_${safeFileName}`);
    tempFilesToClean.push(rawTempFilePath);

    await saveAsyncIterableToTempFileWithProgress(
      job,
      readableStreamToAsyncIterable(responseStream),
      rawTempFilePath,
      signal
    );

    let finalTempPath = rawTempFilePath;
    if (effectiveCompressMode !== 'none') {
      if (job.chatId && job.statusMessageId) {
        await editTelegramMessage(
          job.chatId,
          job.statusMessageId,
          `📦 <b>جاري ضغط الملف قبل إرساله إلى تليجرام (${formatCompressModeAr(effectiveCompressMode)})...</b>\n` +
            `📄 <b>الملف:</b> <code>${job.fileName}</code>`,
          cancelKeyboard
        );
      }

      const compResult = await compressLocalFile(
        rawTempFilePath,
        job.fileName,
        job.mimeType,
        effectiveCompressMode,
        signal
      );

      if (compResult.finalPath !== rawTempFilePath) {
        tempFilesToClean.push(compResult.finalPath);
      }
      finalTempPath = compResult.finalPath;
      job.fileName = compResult.finalFileName;
      job.mimeType = compResult.finalMimeType;
    }

    const finalStat = fs.statSync(finalTempPath);
    job.totalBytes = finalStat.size;
    job.bytesTransferred = finalStat.size;

    if (job.totalBytes > 2000 * 1024 * 1024) {
      throw new Error('حجم الملف يتجاوز الحد الأقصى المسموح به في منصة تليجرام (2GB).');
    }

    job.status = 'uploading';
    saveStateToDisk();

    if (job.chatId && job.statusMessageId) {
      await editTelegramMessage(
        job.chatId,
        job.statusMessageId,
        `📲 <b>تم تحضير الملف (${formatBytes(job.totalBytes)}) وجاري رفعه وإرساله إلى محادثة تليجرام...</b>\n` +
          `📄 <b>الملف:</b> <code>${job.fileName}</code>`,
        cancelKeyboard
      );
    }

    let lastTgProgressEdit = 0;
    const caption =
      `📲 <b>تم سحب الملف وإرساله إلى تليجرام بنجاح!</b>\n` +
      `📄 <b>الاسم:</b> <code>${job.fileName}</code>\n` +
      `📦 <b>الحجم:</b> ${formatBytes(job.totalBytes)}`;

    await sendLocalFileToTelegramChat(
      targetChatId,
      finalTempPath,
      job.fileName,
      job.totalBytes,
      caption,
      signal,
      (uploadPct) => {
        const now = Date.now();
        if (job.chatId && job.statusMessageId && now - lastTgProgressEdit > 3000) {
          lastTgProgressEdit = now;
          editTelegramMessage(
            job.chatId,
            job.statusMessageId,
            `📲 <b>جاري رفع الملف إلى تليجرام (${uploadPct}%)...</b>\n` +
              `📄 <b>الملف:</b> <code>${job.fileName}</code>\n` +
              `📦 <b>الحجم:</b> ${formatBytes(job.totalBytes)}`,
            cancelKeyboard
          );
        }
      }
    );

    jobAbortControllers.delete(job.id);
    job.status = 'completed';
    job.completedAt = new Date().toISOString();
    saveStateToDisk();

    if (job.chatId && job.statusMessageId) {
      await editTelegramMessage(
        job.chatId,
        job.statusMessageId,
        `✅ <b>اكتمل سحب وإرسال الملف إلى تليجرام بنجاح!</b>\n` +
          `📄 <b>الملف:</b> <code>${job.fileName}</code> (${formatBytes(job.totalBytes)})`,
        {
          inline_keyboard: [
            [
              { text: '📥 سحب ملف آخر من Drive', callback_data: 'menu_pull_from_drive' },
              { text: '🏠 القائمة الرئيسية', callback_data: 'open_main' },
            ],
          ],
        }
      );
    }
  } catch (error: any) {
    jobAbortControllers.delete(job.id);
    const rawMsg = error?.cause?.message || error?.message || 'حدث خطأ أثناء سحب وإرسال الملف إلى تليجرام.';
    if (rawMsg === 'CANCELLED_BY_USER' || signal.aborted || (job.status as string) === 'cancelled') {
      job.status = 'cancelled';
      job.speedBps = 0;
      job.errorMessage = 'تم إلغاء سحب الملف بناءً على طلب المستخدم.';
      saveStateToDisk();
      return;
    }

    job.status = 'failed';
    job.errorMessage = rawMsg;
    saveStateToDisk();

    if (job.chatId && job.statusMessageId) {
      await editTelegramMessage(
        job.chatId,
        job.statusMessageId,
        `❌ <b>تعذر سحب وإرسال الملف إلى تليجرام</b>\n\n` +
          `📄 <b>الملف:</b> <code>${job.fileName}</code>\n` +
          `⚠️ <b>السبب:</b> ${job.errorMessage}`,
        {
          inline_keyboard: [
            [
              { text: '🔄 إعادة المحاولة', callback_data: `retry_${job.id}` },
              { text: '🗑️ حذف من السجل', callback_data: `delete_${job.id}` },
            ],
            [{ text: '🏠 القائمة الرئيسية', callback_data: 'open_main' }],
          ],
        }
      );
    }
  } finally {
    for (const f of tempFilesToClean) {
      if (f && fs.existsSync(f)) {
        try {
          fs.unlinkSync(f);
        } catch {
          // Ignore temp file cleanup error
        }
      }
    }
  }
}

async function processPendingQueue(filterChatId?: number, filterEmail?: string): Promise<void> {
  const waitingJobs = transferJobs.filter((j) => {
    if (j.status !== 'waiting_auth' && j.status !== 'queued') return false;
    if (filterChatId && j.chatId && j.chatId !== filterChatId) return false;
    if (filterEmail && j.accountEmail && j.accountEmail !== 'default' && j.accountEmail !== filterEmail) return false;
    return true;
  });
  for (const job of waitingJobs) {
    const sess = resolveJobDriveSession(job);
    if (job.direction === 'to_telegram' || job.source === 'drive_to_telegram' || job.source === 'url_to_telegram') {
      await executePullToTelegramJob(job);
    } else if (sess.accessToken && sess.accountEnabled) {
      await executeTransferJob(job);
    }
  }
}

function buildUrlPromptMessageAndKeyboard(choiceId: string): {
  text: string;
  replyMarkup: { inline_keyboard: any[][] };
} {
  const pending = pendingUrlChoices.get(choiceId);
  const rawUrl = pending?.url || '';
  const selectedQ = pending?.selectedQuality || adminConfig.defaultQuality || '720';
  const compMode: CompressMode = pending?.compressMode || adminConfig.defaultCompressMode || 'none';
  const videoPlatform = detectVideoPlatform(rawUrl);
  const appUrl = getAppUrl();

  const compLabelBtn =
    compMode === 'zip'
      ? '📦 الضغط قبل النقل: أرشيف ZIP (.zip) ✅'
      : compMode === 'media'
      ? '📦 الضغط قبل النقل: تقليص حجم الميديا ✅'
      : '📦 الضغط قبل النقل: بدون ضغط ⚪';

  if (videoPlatform.isVideoPlatform) {
    const qualities = ['1080', '720', '480', '360', '240'];
    const qualityBtns = qualities.map((q) => ({
      text: `${selectedQ === q ? '✅ ' : '🎬 '}${q}p`,
      callback_data: `set_url_q_${q}_${choiceId}`,
    }));

    const rows: any[][] = [
      qualityBtns.slice(0, 3),
      qualityBtns.slice(3),
      [{ text: compLabelBtn, callback_data: `toggle_url_comp_${choiceId}` }],
      [
        {
          text: `📲 سحب فيديو (${selectedQ}p) إلى تليجرام`,
          callback_data: `url_to_tg_${choiceId}`,
        },
      ],
      [
        {
          text: `☁️ رفع فيديو (${selectedQ}p) إلى Google Drive`,
          callback_data: `url_to_drive_${choiceId}`,
        },
      ],
      [
        { text: '🎵 سحب صوت (MP3 320k) لتليجرام', callback_data: `url_audio_tg_${choiceId}` },
        { text: '🎵 صوت (MP3) إلى Drive', callback_data: `url_audio_drive_${choiceId}` },
      ],
    ];

    if (appUrl && appUrl.startsWith('https://')) {
      const dlVideoUrl = `${appUrl}/api/direct-download?url=${encodeURIComponent(
        rawUrl
      )}&format=video&quality=${encodeURIComponent(selectedQ)}&compress=${encodeURIComponent(compMode)}`;
      const dlAudioUrl = `${appUrl}/api/direct-download?url=${encodeURIComponent(
        rawUrl
      )}&format=audio&quality=320&compress=${encodeURIComponent(compMode)}`;
      rows.push([
        { text: `📥 تحميل مباشر للجهاز (فيديو ${selectedQ}p)`, url: dlVideoUrl },
        { text: '📥 تحميل مباشر (صوت MP3)', url: dlAudioUrl },
      ]);
    }

    rows.push([{ text: '⚙️ بوابة الإعدادات', callback_data: 'portal_settings' }]);

    const text =
      `🎬 <b>تم التعرف على رابط ${videoPlatform.platformName}!</b>\n` +
      `🔗 <code>${rawUrl}</code>\n\n` +
      `• <b>جودة الفيديو المحددة:</b> <code>${selectedQ}p</code>\n` +
      `• <b>خيار ضغط الملف:</b> ${formatCompressModeAr(compMode)}\n\n` +
      `👇 <b>اختر الجودة وخيار الضغط ثم اضغط على الوجهة أو التحميل المباشر:</b>`;

    return { text, replyMarkup: { inline_keyboard: rows } };
  }

  const fileName = extractFilenameFromUrl(rawUrl);
  const rows: any[][] = [
    [{ text: compLabelBtn, callback_data: `toggle_url_comp_${choiceId}` }],
    [{ text: '☁️ رفعه إلى حسابي Google Drive', callback_data: `url_to_drive_${choiceId}` }],
    [{ text: '📲 سحبه وإرساله كملف هنا في تليجرام', callback_data: `url_to_tg_${choiceId}` }],
  ];

  if (appUrl && appUrl.startsWith('https://')) {
    const dlFileUrl = `${appUrl}/api/direct-download?url=${encodeURIComponent(
      rawUrl
    )}&compress=${encodeURIComponent(compMode)}`;
    rows.push([{ text: '📥 تحميل الملف مباشرة إلى جهازك', url: dlFileUrl }]);
  }

  rows.push([{ text: '⚙️ بوابة الإعدادات', callback_data: 'portal_settings' }]);

  const text =
    `🔗 <b>تم استلام الرابط بنجاح!</b>\n` +
    `📄 <b>الملف المكتشف:</b> <code>${fileName}</code>\n` +
    `📦 <b>وضع الضغط قبل النقل:</b> ${formatCompressModeAr(compMode)}\n\n` +
    `👇 <b>اختر ضغط الملف أو وجهته أو التحميل المباشر:</b>`;

  return { text, replyMarkup: { inline_keyboard: rows } };
}

// ============================================================================
// Callback Query Handler (Interactive Portals & Buttons Inside Telegram)
// ============================================================================

function syncLegacyOwnerGlobalsIfOwner(chatId: number, prof: UserDriveProfile): void {
  if (!adminConfig.ownerChatId || adminConfig.ownerChatId === chatId) {
    driveSession.accessToken = prof.accessToken;
    driveSession.userEmail = prof.userEmail;
    driveSession.userName = prof.userName;
    driveSession.activeFolderId = prof.activeFolderId;
    driveSession.activeFolderName = prof.activeFolderName || 'Telegram Bot Uploads';
    adminConfig.accountEnabled = prof.accountEnabled;
    autoCategorizeByType = prof.autoCategorizeByType;
    skipDuplicates = prof.skipDuplicates;
    adminConfig.urlHandlingMode = prof.urlHandlingMode;
    adminConfig.defaultQuality = prof.defaultQuality;
    adminConfig.defaultCompressMode = prof.defaultCompressMode;
  }
}

async function handleCallbackQuery(callbackQuery: any): Promise<void> {
  const cbId = callbackQuery.id;
  const data: string = callbackQuery.data || '';
  const msg = callbackQuery.message;
  const chatId: number | undefined = msg?.chat?.id;
  const messageId: number | undefined = msg?.message_id;
  const callerName =
    [callbackQuery.from?.first_name, callbackQuery.from?.last_name].filter(Boolean).join(' ') || 'مستخدم تليجرام';
  const callerUsername = callbackQuery.from?.username;

  const answerCallback = async (text?: string, showAlert = false) => {
    try {
      await telegramApi('answerCallbackQuery', {
        callback_query_id: cbId,
        text,
        show_alert: showAlert,
      });
    } catch {
      // Ignore
    }
  };

  if (!chatId || !messageId) {
    await answerCallback();
    return;
  }

  // Auto-claim owner if none is set yet
  if (!adminConfig.ownerChatId) {
    adminConfig.ownerChatId = chatId;
    adminConfig.ownerName = callerName;
    adminConfig.ownerUsername = callerUsername || null;
    saveStateToDisk();
  }

  const userSess = getEffectiveSessionForChat(chatId);
  const prof = userSess.profile;

  // Main menu & refresh
  if (data === 'open_main' || data === 'open_settings' || data === 'refresh_status') {
    awaitingFolderNameChats.delete(chatId);
    awaitingUrlToTelegramChats.delete(chatId);
    awaitingDriveSearchChats.delete(chatId);
    await answerCallback('تم فتح القائمة الرئيسية ✅');
    await editTelegramMessage(chatId, messageId, buildControlPanelText(chatId), buildMainControlKeyboard(chatId));
    return;
  }

  // 1. Settings Portal (بوابة الإعدادات والحساب الشخصي)
  if (data === 'portal_settings') {
    await answerCallback('⚙️ بوابة الإعدادات والحساب الشخصي');
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'cycle_default_quality') {
    const order = ['1080', '720', '480', '360', '240'];
    const idx = order.indexOf(prof.defaultQuality || '720');
    prof.defaultQuality = order[(idx + 1) % order.length];
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback(`تم ضبط الجودة الافتراضية لحسابك إلى ${prof.defaultQuality}p 🎬`);
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'cycle_default_compress') {
    const order: CompressMode[] = ['none', 'zip', 'media'];
    const idx = order.indexOf(prof.defaultCompressMode || 'none');
    prof.defaultCompressMode = order[(idx + 1) % order.length];
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback(`تم ضبط وضع الضغط لحسابك: ${formatCompressModeAr(prof.defaultCompressMode)} 📦`);
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'toggle_account_enabled') {
    prof.accountEnabled = !prof.accountEnabled;
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    if (prof.accountEnabled && userSess.accessToken) {
      processPendingQueue(chatId, prof.userEmail || undefined).catch(() => {});
    }
    await answerCallback(
      prof.accountEnabled
        ? 'تم تفعيل استقبال حسابك بنجاح 🟢'
        : 'تم إيقاف استقبال حسابك مؤقتاً ⏸️'
    );
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'confirm_unlink_drive') {
    await answerCallback();
    await editTelegramMessage(
      chatId,
      messageId,
      `⚠️ <b>تأكيد إلغاء ربط حسابك الشخصي في Google Drive</b>\n\n` +
        `الحساب الحالي: <code>${userSess.userEmail || 'متصل'}</code>\n` +
        `هل أنت متأكد من رغبتك في فصل وإلغاء ربط هذا الحساب من محادثتك؟`,
      {
        inline_keyboard: [
          [
            { text: '🔌 نعم، إلغاء ربط حسابي الآن', callback_data: 'unlink_drive_now' },
            { text: '🔙 تراجع', callback_data: 'portal_settings' },
          ],
        ],
      }
    );
    return;
  }

  if (data === 'unlink_drive_now') {
    prof.accessToken = null;
    prof.userEmail = null;
    prof.userName = null;
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback('تم إلغاء ربط حسابك في Google Drive بنجاح 🔌', true);
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'toggle_url_mode') {
    const order: ('ask' | 'to_drive' | 'to_telegram')[] = ['ask', 'to_drive', 'to_telegram'];
    const nextIdx = (order.indexOf(prof.urlHandlingMode) + 1) % order.length;
    prof.urlHandlingMode = order[nextIdx];
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback('تم تغيير وضع التعامل مع الروابط لحسابك ✅');
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'toggle_categorize') {
    prof.autoCategorizeByType = !prof.autoCategorizeByType;
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback(
      prof.autoCategorizeByType
        ? 'تم تفعيل الفرز التلقائي للملفات حسب النوع لحسابك ✅'
        : 'تم إيقاف الفرز التلقائي ✅'
    );
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'toggle_dedup') {
    prof.skipDuplicates = !prof.skipDuplicates;
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback(
      prof.skipDuplicates
        ? 'تم تفعيل منع رفع الملفات المكررة لنفس الحساب ✅'
        : 'تم إيقاف منع التكرار'
    );
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  // 2. Owner Admin Portal (بوابة الإدارة للمالك)
  if (data === 'portal_admin') {
    await answerCallback('🛡️ بوابة الإدارة والتحكم للمالك');
    await editTelegramMessage(chatId, messageId, buildAdminPortalText(chatId), buildAdminPortalKeyboard(chatId));
    return;
  }

  if (data === 'claim_owner') {
    adminConfig.ownerChatId = chatId;
    adminConfig.ownerName = callerName;
    adminConfig.ownerUsername = callerUsername || null;
    saveStateToDisk();
    await answerCallback('تم تعيين حسابك كمالك رسمي للبوت والموقع 👑', true);
    await editTelegramMessage(chatId, messageId, buildAdminPortalText(chatId), buildAdminPortalKeyboard(chatId));
    return;
  }

  if (data === 'toggle_bot_power') {
    if (adminConfig.ownerChatId && adminConfig.ownerChatId !== chatId) {
      await answerCallback('هذا الخيار مخصص لمالك البوت فقط 🔒', true);
      return;
    }
    adminConfig.botPaused = !adminConfig.botPaused;
    saveStateToDisk();
    await answerCallback(adminConfig.botPaused ? 'تم إيقاف البوت مؤقتاً ⏸️' : 'تم تشغيل البوت 🟢');
    await editTelegramMessage(chatId, messageId, buildAdminPortalText(chatId), buildAdminPortalKeyboard(chatId));
    return;
  }

  if (data === 'toggle_access_mode') {
    if (adminConfig.ownerChatId && adminConfig.ownerChatId !== chatId) {
      await answerCallback('هذا الخيار مخصص لمالك البوت فقط 🔒', true);
      return;
    }
    adminConfig.accessMode = adminConfig.accessMode === 'public' ? 'owner_only' : 'public';
    saveStateToDisk();
    await answerCallback(
      adminConfig.accessMode === 'owner_only'
        ? 'أصبح البوت خاصاً بالمالك فقط 🔒'
        : 'أصبح البوت متاحاً لجميع المستخدمين عبر حساباتهم الشخصية 🌍'
    );
    await editTelegramMessage(chatId, messageId, buildAdminPortalText(chatId), buildAdminPortalKeyboard(chatId));
    return;
  }

  if (data === 'admin_users_list') {
    const users = Object.values(adminConfig.knownUsers);
    const rows: any[][] = [];
    for (const u of users.slice(0, 10)) {
      rows.push([
        {
          text: `${u.blocked ? '🚫 محظور: ' : '👤 '}${u.name} (${u.transfersCount} ملف) — اضغط ${
            u.blocked ? 'لفك الحظر' : 'للحظر'
          }`,
          callback_data: `toggle_block_user_${u.chatId}`,
        },
      ]);
    }
    rows.push([{ text: '🔙 رجوع لبوابة الإدارة', callback_data: 'portal_admin' }]);

    const text =
      `👥 <b>قائمة المستخدمين المسجلين في البوت (${users.length}):</b>\n\n` +
      (users.length === 0
        ? 'لا يوجد مستخدمون مسجلون بعد.'
        : users
            .slice(0, 15)
            .map((u, i) => {
              const uSess = getEffectiveSessionForChat(u.chatId);
              const linkedEmail = uSess.userEmail ? ` (${uSess.userEmail})` : '';
              return `${i + 1}. <b>${u.name}</b> ${u.username ? `(@${u.username})` : ''}${linkedEmail} — <code>${
                u.chatId
              }</code> — ${u.blocked ? '🚫 محظور' : '🟢 مسموح'}`;
            })
            .join('\n')) +
      `\n\nاضغط على أي مستخدم أدناه لحظره أو فك الحظر عنه:`;

    await answerCallback();
    await editTelegramMessage(chatId, messageId, text, { inline_keyboard: rows });
    return;
  }

  if (data.startsWith('toggle_block_user_')) {
    if (adminConfig.ownerChatId && adminConfig.ownerChatId !== chatId) {
      await answerCallback('للمالك فقط 🔒', true);
      return;
    }
    const targetId = data.replace('toggle_block_user_', '');
    const targetUser = adminConfig.knownUsers[targetId];
    if (targetUser) {
      if (Number(targetId) === adminConfig.ownerChatId) {
        await answerCallback('لا يمكن حظر مالك البوت!', true);
        return;
      }
      targetUser.blocked = !targetUser.blocked;
      saveStateToDisk();
      await answerCallback(targetUser.blocked ? 'تم حظر المستخدم 🚫' : 'تم فك الحظر عن المستخدم 🟢');
    }
    callbackQuery.data = 'admin_users_list';
    await handleCallbackQuery(callbackQuery);
    return;
  }

  if (data === 'admin_restart_mtproto') {
    await answerCallback('جاري إعادة تنشيط محرك MTProto 2GB...');
    await startMtprotoEngine();
    await editTelegramMessage(chatId, messageId, buildAdminPortalText(chatId), buildAdminPortalKeyboard(chatId));
    return;
  }

  if (data === 'admin_clear_all_history') {
    if (adminConfig.ownerChatId && adminConfig.ownerChatId !== chatId) {
      await answerCallback('للمالك فقط 🔒', true);
      return;
    }
    const active = getActiveJobsList();
    for (const j of active) {
      cancelTransferJobById(j.id);
    }
    transferJobs.length = 0;
    saveStateToDisk();
    await answerCallback('تم مسح سجل جميع العمليات بالكامل 🧹', true);
    await editTelegramMessage(chatId, messageId, buildAdminPortalText(chatId), buildAdminPortalKeyboard(chatId));
    return;
  }

  // 3. Active Transfers Live Monitor (إظهار عمليات الرفع الحالية)
  if (data === 'view_active_transfers') {
    await answerCallback('📡 تم تحديث قائمة العمليات الجارية');
    await editTelegramMessage(chatId, messageId, buildActiveTransfersText(chatId), buildActiveTransfersKeyboard(chatId));
    return;
  }

  // 4. Pull Files from Google Drive to Telegram (سحب الملفات من حساب درايف إلى تليجرام)
  if (data === 'menu_pull_from_drive') {
    if (!userSess.accessToken) {
      await answerCallback('يرجى ربط أو تنشيط حسابك الشخصي في Google Drive أولاً', true);
      return;
    }
    try {
      await answerCallback('جاري جلب ملفاتك من Google Drive...');
      const files = await listDriveFilesForTelegram(userSess.accessToken);
      const baseAppUrl = (process.env.APP_URL || '').replace(/\/+$/, '');
      const rows: any[][] = [];
      for (const f of files.slice(0, 8)) {
        const sizeStr = f.size ? formatBytes(parseInt(f.size, 10)) : 'ملف';
        const shortName = f.name.length > 22 ? f.name.slice(0, 20) + '…' : f.name;
        const row: any[] = [
          {
            text: `📲 ${shortName} (${sizeStr})`,
            callback_data: `pull_drive_${f.id}`,
          },
        ];
        if (baseAppUrl && baseAppUrl.startsWith('https://')) {
          row.push({
            text: '📥 تحميل للجهاز',
            url: `${baseAppUrl}/api/direct-download?driveFileId=${encodeURIComponent(
              f.id
            )}&chatId=${encodeURIComponent(String(chatId))}`,
          });
        }
        rows.push(row);
      }
      rows.push([
        { text: '🔍 بحث عن ملف بالاسم في Drive', callback_data: 'prompt_search_drive_for_tg' },
        { text: '🔄 تحديث القائمة', callback_data: 'menu_pull_from_drive' },
      ]);
      rows.push([{ text: '🔙 رجوع للقائمة الرئيسية', callback_data: 'open_main' }]);

      await editTelegramMessage(
        chatId,
        messageId,
        `📥 <b>سحب الملفات من حسابك الشخصي Google Drive (${userSess.userEmail || 'متصل'}) إلى تليجرام</b>\n\n` +
          `اضغط <b>📲</b> لإرسال الملف إلى محادثة تليجرام، أو <b>📥 تحميل للجهاز</b> لتحميله مباشرة عبر المتصفح:`,
        { inline_keyboard: rows }
      );
    } catch (err: any) {
      await answerCallback(err?.message || 'تعذر جلب ملفات Drive', true);
    }
    return;
  }

  if (data === 'prompt_search_drive_for_tg') {
    awaitingDriveSearchChats.add(chatId);
    await answerCallback('أرسل اسم الملف للبحث عنه في Drive');
    await sendTelegramMessage(
      chatId,
      `🔍 <b>البحث في حسابك Google Drive لسحب ملف إلى تليجرام:</b>\n\nأرسل الآن جزءاً من <b>اسم الملف</b> في رسالة عادية، وسيعرض لك البوت جميع الملفات المطابقة لإرسالها فوراً إلى تليجرام!`,
      messageId,
      {
        inline_keyboard: [[{ text: '❌ إلغاء', callback_data: 'open_main' }]],
      }
    );
    return;
  }

  if (data.startsWith('pull_drive_')) {
    const driveFileId = data.replace('pull_drive_', '');
    if (!userSess.accessToken) {
      await answerCallback('يرجى ربط حساب Google Drive أولاً', true);
      return;
    }

    await answerCallback('جاري بدء سحب الملف من Google Drive وإرساله إلى تليجرام 📲');
    const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
    const statusMsgId = await sendTelegramMessage(
      chatId,
      `📥 <b>جاري تحضير وسحب الملف من Google Drive لإرساله إلى تليجرام...</b>`,
      undefined,
      {
        inline_keyboard: [[{ text: '⛔ إلغاء السحب', callback_data: `cancel_${jobId}` }]],
      }
    );

    const job: TransferJob = {
      id: jobId,
      source: 'drive_to_telegram',
      direction: 'to_telegram',
      compressMode: userSess.defaultCompressMode || 'none',
      fileName: `drive_file_${driveFileId.slice(0, 6)}`,
      mimeType: 'application/octet-stream',
      totalBytes: 0,
      bytesTransferred: 0,
      speedBps: 0,
      status: 'queued',
      senderName: callerName,
      senderUsername: callerUsername,
      accountEmail: userSess.userEmail || 'default',
      chatId,
      statusMessageId: statusMsgId,
      driveFileId,
      createdAt: new Date().toISOString(),
    };

    transferJobs.unshift(job);
    saveStateToDisk();
    executePullToTelegramJob(job);
    return;
  }

  // 5. Pull External URL to Telegram (سحب رابط من أي منصة إلى تليجرام)
  if (data === 'prompt_url_to_telegram') {
    awaitingUrlToTelegramChats.add(chatId);
    await answerCallback('أرسل رابط يوتيوب أو تيك توك أو أي منصة ليتم سحبه إلى تليجرام');
    await sendTelegramMessage(
      chatId,
      `🌐 <b>سحب فيديو أو ملف من أي منصة عبر الرابط إلى تليجرام:</b>\n\n` +
        `أرسل الآن أي رابط من:\n` +
        `• 🎬 <b>YouTube</b> (فيديوهات يوتيوب + Shorts بجودة 1080p/720p/480p/360p أو صوت MP3)\n` +
        `• 📱 <b>TikTok</b> (فيديوهات تيك توك بدون علامة مائية)\n` +
        `• ☁️ <b>Google Drive / MediaFire / Dropbox / GitHub / OneDrive</b>\n\n` +
        `وسيقوم البوت بسحبه وإرساله كملف أو فيديو مباشر داخل محادثة تليجرام!`,
      messageId,
      {
        inline_keyboard: [[{ text: '❌ إلغاء', callback_data: 'open_main' }]],
      }
    );
    return;
  }

  // Interactive Quality & Compression Toggles on URL Prompt
  if (data.startsWith('set_url_q_')) {
    const rest = data.replace('set_url_q_', '');
    const firstUnderscore = rest.indexOf('_');
    if (firstUnderscore !== -1) {
      const q = rest.slice(0, firstUnderscore);
      const choiceId = rest.slice(firstUnderscore + 1);
      const pending = pendingUrlChoices.get(choiceId);
      if (pending) {
        pending.selectedQuality = q;
        await answerCallback(`تم تحديد الجودة: ${q}p ✅`);
        const built = buildUrlPromptMessageAndKeyboard(choiceId);
        await editTelegramMessage(chatId, messageId, built.text, built.replyMarkup);
        return;
      }
    }
    await answerCallback('انتهت صلاحية هذا الرابط، أرسله مجدداً', true);
    return;
  }

  if (data.startsWith('toggle_url_comp_')) {
    const choiceId = data.replace('toggle_url_comp_', '');
    const pending = pendingUrlChoices.get(choiceId);
    if (pending) {
      const order: CompressMode[] = ['none', 'zip', 'media'];
      const next = order[(order.indexOf(pending.compressMode || 'none') + 1) % order.length];
      pending.compressMode = next;
      await answerCallback(`وضع الضغط: ${formatCompressModeAr(next)} 📦`);
      const built = buildUrlPromptMessageAndKeyboard(choiceId);
      await editTelegramMessage(chatId, messageId, built.text, built.replyMarkup);
      return;
    }
    await answerCallback('انتهت صلاحية هذا الرابط، أرسله مجدداً', true);
    return;
  }

  if (
    data.startsWith('url_to_drive_') ||
    data.startsWith('url_to_tg_') ||
    data.startsWith('url_audio_drive_') ||
    data.startsWith('url_audio_tg_')
  ) {
    const isToTg = data.startsWith('url_to_tg_') || data.startsWith('url_audio_tg_');
    const isAudio = data.startsWith('url_audio_drive_') || data.startsWith('url_audio_tg_');
    const prefix = data.startsWith('url_audio_tg_')
      ? 'url_audio_tg_'
      : data.startsWith('url_audio_drive_')
      ? 'url_audio_drive_'
      : data.startsWith('url_to_tg_')
      ? 'url_to_tg_'
      : 'url_to_drive_';
    const choiceId = data.replace(prefix, '');
    const pending = pendingUrlChoices.get(choiceId);
    if (!pending) {
      await answerCallback('انتهت صلاحية هذا الاختيار، أرسل الرابط مرة أخرى', true);
      return;
    }
    pendingUrlChoices.delete(choiceId);

    const chosenQuality = isAudio ? '320' : pending.selectedQuality || userSess.defaultQuality || '720';
    const chosenCompress: CompressMode = pending.compressMode || userSess.defaultCompressMode || 'none';
    const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
    const fileName = extractFilenameFromUrl(pending.url, isAudio ? 'audio' : 'video');

    await answerCallback(
      isToTg
        ? isAudio
          ? 'جاري سحب الصوت (MP3) إلى تليجرام 🎵'
          : `جاري سحب الفيديو (${chosenQuality}p) إلى تليجرام 📲`
        : isAudio
        ? 'جاري رفع الصوت (MP3) إلى Google Drive ☁️'
        : `جاري رفع الفيديو (${chosenQuality}p) إلى Google Drive ☁️`
    );
    await editTelegramMessage(
      chatId,
      messageId,
      isToTg
        ? `📥 <b>جاري استخراج وسحب ${isAudio ? 'الصوت (MP3)' : `الفيديو/الملف (${chosenQuality}p)`}${
            chosenCompress !== 'none' ? ` مع الضغط (${formatCompressModeAr(chosenCompress)})` : ''
          } لإرساله إلى تليجرام...</b>\n📄 <code>${fileName}</code>`
        : `☁️ <b>جاري استخراج ورفع ${isAudio ? 'الصوت (MP3)' : `الفيديو/الملف (${chosenQuality}p)`}${
            chosenCompress !== 'none' ? ` مع الضغط (${formatCompressModeAr(chosenCompress)})` : ''
          } إلى Google Drive...</b>\n📄 <code>${fileName}</code>`,
      {
        inline_keyboard: [[{ text: '⛔ إلغاء العملية', callback_data: `cancel_${jobId}` }]],
      }
    );

    const job: TransferJob = {
      id: jobId,
      source: isToTg ? 'url_to_telegram' : 'url',
      direction: isToTg ? 'to_telegram' : 'to_drive',
      protocol: 'http',
      mediaFormat: isAudio ? 'audio' : 'video',
      quality: chosenQuality,
      compressMode: chosenCompress,
      fileName,
      mimeType: isAudio ? 'audio/mpeg' : 'application/octet-stream',
      totalBytes: 0,
      bytesTransferred: 0,
      speedBps: 0,
      status: isToTg || (userSess.accessToken && userSess.accountEnabled) ? 'queued' : 'waiting_auth',
      senderName: pending.senderName,
      senderUsername: pending.senderUsername,
      accountEmail: userSess.userEmail || 'default',
      chatId,
      messageId: pending.messageId,
      statusMessageId: messageId,
      directUrl: pending.url,
      folderName: userSess.activeFolderName,
      createdAt: new Date().toISOString(),
    };

    transferJobs.unshift(job);
    saveStateToDisk();

    if (isToTg) {
      if (IS_VERCEL) await executePullToTelegramJob(job);
      else executePullToTelegramJob(job);
    } else if (userSess.accessToken && userSess.accountEnabled) {
      if (IS_VERCEL) await executeTransferJob(job);
      else executeTransferJob(job);
    }
    return;
  }

  // Cancel & Delete handlers
  if (data.startsWith('cancel_') && data !== 'cancel_all_active' && data !== 'cancel_folder_prompt') {
    const jobId = data.replace('cancel_', '');
    const cancelled = cancelTransferJobById(jobId);
    if (cancelled) {
      await answerCallback('تم إلغاء العملية فوراً 🚫');
    } else {
      await answerCallback('العملية غير موجودة أو مكتملة مسبقاً');
    }
    return;
  }

  if (data === 'cancel_all_active') {
    const active = getActiveJobsList(chatId);
    for (const j of active) {
      cancelTransferJobById(j.id);
    }
    await answerCallback(`تم إلغاء ${active.length} عمليات جارية 🚫`);
    await editTelegramMessage(chatId, messageId, buildControlPanelText(chatId), buildMainControlKeyboard(chatId));
    return;
  }

  if (data.startsWith('delete_')) {
    const jobId = data.replace('delete_', '');
    const idx = transferJobs.findIndex((j) => j.id === jobId);
    if (idx !== -1) {
      const controller = jobAbortControllers.get(jobId);
      if (controller) {
        controller.abort();
        jobAbortControllers.delete(jobId);
      }
      transferJobs.splice(idx, 1);
      saveStateToDisk();
    }
    await answerCallback('تم حذف العملية من السجل 🗑️');
    await deleteTelegramMessageSafe(chatId, messageId);
    return;
  }

  if (data === 'clear_failed_jobs') {
    const removedCount = clearAllFailedAndCancelledJobs(chatId);
    await answerCallback(`تم حذف ${removedCount} ملفات فاشلة/ملغاة من سجلك 🗑️`);
    await editTelegramMessage(chatId, messageId, buildControlPanelText(chatId), buildMainControlKeyboard(chatId));
    return;
  }

  if (data === 'prompt_new_folder') {
    awaitingFolderNameChats.add(chatId);
    await answerCallback('أرسل الآن اسم المجلد الجديد في رسالة');
    await sendTelegramMessage(
      chatId,
      `📁 <b>إنشاء أو تحديد مجلد جديد في حسابك Google Drive:</b>\n\nأرسل الآن <b>اسم المجلد</b> الذي تريده في رسالة عادية هنا (مثلاً: <code>محاضرات الباطنية</code>)، وسيقوم البوت بإنشائه وتفعيله فوراً في حسابك!`,
      messageId,
      {
        inline_keyboard: [[{ text: '❌ إلغاء', callback_data: 'cancel_folder_prompt' }]],
      }
    );
    return;
  }

  if (data === 'cancel_folder_prompt') {
    awaitingFolderNameChats.delete(chatId);
    awaitingUrlToTelegramChats.delete(chatId);
    awaitingDriveSearchChats.delete(chatId);
    await answerCallback('تم الإلغاء');
    await editTelegramMessage(chatId, messageId, buildControlPanelText(chatId), buildMainControlKeyboard(chatId));
    return;
  }

  if (data === 'menu_folders') {
    if (!userSess.accessToken) {
      await answerCallback('يرجى تسجيل الدخول إلى حسابك Google Drive من لوحة التحكم أولاً', true);
      return;
    }

    try {
      const folders = await listDriveFolders(userSess.accessToken);
      const keyboardRows: any[][] = [];

      for (const f of folders.slice(0, 10)) {
        cachedFoldersById.set(f.id, f.name);
        const isCurrent = userSess.activeFolderId === f.id;
        keyboardRows.push([
          {
            text: `${isCurrent ? '✅ ' : '📁 '}${f.name}`,
            callback_data: `setfolder_${f.id}`,
          },
        ]);
      }

      keyboardRows.push([
        { text: '➕ إنشاء مجلد جديد', callback_data: 'prompt_new_folder' },
        { text: '🔙 رجوع للإعدادات', callback_data: 'portal_settings' },
      ]);

      await answerCallback();
      await editTelegramMessage(
        chatId,
        messageId,
        `📁 <b>اختر مجلد الحفظ في حسابك Google Drive (${userSess.userEmail || 'متصل'}):</b>\nالمجلد النشط حالياً: <code>${userSess.activeFolderName}</code>\n\nاضغط على أي مجلد من القائمة أدناه لتفعيله فوراً:`,
        { inline_keyboard: keyboardRows }
      );
    } catch (err: any) {
      await answerCallback(err?.message || 'تعذر جلب المجلدات', true);
    }
    return;
  }

  if (data.startsWith('setfolder_')) {
    const folderId = data.replace('setfolder_', '');
    const folderName = cachedFoldersById.get(folderId) || userSess.activeFolderName;
    prof.activeFolderId = folderId;
    prof.activeFolderName = folderName;
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();
    await answerCallback(`تم تفعيل المجلد لحسابك: ${folderName} ✅`);
    await editTelegramMessage(chatId, messageId, buildSettingsPortalText(chatId), buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (data === 'list_recent_files') {
    const userJobs = getJobsForUser(chatId, userSess.userEmail);
    const completed = userJobs.filter((j) => j.status === 'completed').slice(0, 10);
    if (completed.length === 0) {
      await answerCallback('لا توجد ملفات مرفوعة في سجلك بعد', true);
      return;
    }

    const lines = completed.map(
      (j, idx) =>
        `${idx + 1}. 📄 <a href="${j.webViewLink || '#'}">${j.fileName}</a> — <code>${formatBytes(
          j.bytesTransferred || j.totalBytes
        )}</code>${j.isDuplicateSkipped ? ' (موجود مسبقاً)' : ''}`
    );

    const text =
      `📄 <b>آخر ${completed.length} ملفات مكتملة في حسابك:</b>\n\n` +
      lines.join('\n') +
      `\n\n📁 المجلد الحالي: <code>${userSess.activeFolderName}</code>`;

    await answerCallback();
    await editTelegramMessage(chatId, messageId, text, {
      inline_keyboard: [
        [
          { text: '📥 سحب ملف من Drive إلى تليجرام', callback_data: 'menu_pull_from_drive' },
          { text: '🔙 القائمة الرئيسية', callback_data: 'open_main' },
        ],
      ],
    });
    return;
  }

  if (data === 'retry_all_failed') {
    const userJobs = getJobsForUser(chatId, userSess.userEmail);
    const toRetry = userJobs.filter((j) => j.status === 'failed' || j.status === 'waiting_auth');
    await answerCallback(`جاري إعادة محاولة ${toRetry.length} ملفات...`);
    for (const job of toRetry) {
      job.status = 'queued';
      job.errorMessage = undefined;
      if (job.direction === 'to_telegram' || job.source === 'drive_to_telegram' || job.source === 'url_to_telegram') {
        executePullToTelegramJob(job);
      } else {
        executeTransferJob(job);
      }
    }
    await editTelegramMessage(chatId, messageId, buildControlPanelText(chatId), buildMainControlKeyboard(chatId));
    return;
  }

  if (data.startsWith('retry_')) {
    const jobId = data.replace('retry_', '');
    const job = transferJobs.find((j) => j.id === jobId);
    if (!job) {
      await answerCallback('لم يتم العثور على العملية', true);
      return;
    }
    await answerCallback('جاري إعادة المحاولة...');
    job.status = 'queued';
    job.errorMessage = undefined;
    if (job.direction === 'to_telegram' || job.source === 'drive_to_telegram' || job.source === 'url_to_telegram') {
      executePullToTelegramJob(job);
    } else {
      executeTransferJob(job);
    }
    return;
  }

  await answerCallback();
}

// ============================================================================
// Telegram Update Processor
// ============================================================================

function extractFilenameFromUrl(urlStr: string, format: 'video' | 'audio' = 'video'): string {
  try {
    const ext = format === 'audio' ? 'mp3' : 'mp4';
    const platform = detectVideoPlatform(urlStr);
    if (platform.isYouTube) {
      const ytId = extractYouTubeId(urlStr) || Date.now();
      return `YouTube_${ytId}.${ext}`;
    }
    if (platform.isTikTok) {
      return `TikTok_${Date.now()}.${ext}`;
    }
    if (platform.isVideoPlatform) {
      return `Video_${Date.now()}.${ext}`;
    }
    const parsed = new URL(urlStr);
    const pathname = decodeURIComponent(parsed.pathname);
    const base = path.basename(pathname);
    if (base && base.includes('.') && base.length < 180) {
      return base;
    }
    return `file_${Date.now()}.bin`;
  } catch {
    return `file_${Date.now()}.bin`;
  }
}

async function handleTelegramUpdate(update: any): Promise<void> {
  if (update.callback_query) {
    await handleCallbackQuery(update.callback_query);
    return;
  }

  const msg = update.message || update.channel_post;
  if (!msg) return;

  const chatId: number = msg.chat.id;
  const messageId: number = msg.message_id;
  const senderName =
    [msg.from?.first_name, msg.from?.last_name].filter(Boolean).join(' ') || msg.chat?.title || 'مستخدم تليجرام';
  const senderUsername = msg.from?.username || msg.chat?.username;
  const text: string = (msg.text || msg.caption || '').trim();

  // Auto-register owner if none set yet
  if (!adminConfig.ownerChatId) {
    adminConfig.ownerChatId = chatId;
    adminConfig.ownerName = senderName;
    adminConfig.ownerUsername = senderUsername || null;
  }

  // Track user in knownUsers
  const existingUser = adminConfig.knownUsers[String(chatId)];
  if (!existingUser) {
    adminConfig.knownUsers[String(chatId)] = {
      chatId,
      name: senderName,
      username: senderUsername,
      lastSeenAt: new Date().toISOString(),
      transfersCount: 0,
      blocked: false,
    };
  } else {
    existingUser.name = senderName;
    existingUser.username = senderUsername;
    existingUser.lastSeenAt = new Date().toISOString();
  }
  saveStateToDisk();

  // Check if user is blocked or access is restricted to owner
  const isOwner = adminConfig.ownerChatId === chatId;
  if (!isOwner) {
    if (adminConfig.knownUsers[String(chatId)]?.blocked) {
      await sendTelegramMessage(chatId, `🚫 عذراً، تم إيقاف صلاحية وصولك إلى هذا البوت من قِبل المالك.`, messageId);
      return;
    }
    if (adminConfig.accessMode === 'owner_only') {
      await sendTelegramMessage(chatId, `🔒 هذا البوت مضبوط حالياً في الوضع الخاص بمالك البوت فقط.`, messageId);
      return;
    }
  }

  // Handle 1-click Telegram account link deep-link (/start link_<CODE>)
  if (text.startsWith('/start')) {
    const startArg = text.replace(/^\/start(@\S+)?\s*/i, '').trim();
    if (startArg.toLowerCase().startsWith('link_')) {
      const code = startArg.slice(5).trim().toUpperCase();
      const matchedProfile = findProfileByLinkCode(code);
      if (matchedProfile) {
        matchedProfile.chatId = chatId;
        matchedProfile.telegramName = senderName;
        matchedProfile.telegramUsername = senderUsername || null;
        // Also merge any temporary tg_<chatId> profile jobs
        for (const j of transferJobs) {
          if (j.chatId === chatId && (!j.accountEmail || j.accountEmail === 'default')) {
            j.accountEmail = matchedProfile.userEmail || 'default';
          }
        }
        saveStateToDisk();
        processPendingQueue(chatId, matchedProfile.userEmail || undefined).catch(() => {});
        await sendTelegramMessage(
          chatId,
          `🎉 <b>تم ربط حسابك في تليجرام بحسابك الشخصي في Google Drive بنجاح!</b>\n\n` +
            `📧 <b>حساب Google المربوط:</b> <code>${matchedProfile.userEmail || 'متصل'}</code>\n` +
            `📁 <b>المجلد النشط:</b> <code>${matchedProfile.activeFolderName || 'Telegram Bot Uploads'}</code>\n\n` +
            `🚀 يمكنك الآن إرسال أي ملف أو رابط هنا ليتم رفعه مباشرة إلى حسابك الشخصي!`,
          messageId,
          buildMainControlKeyboard(chatId)
        );
        return;
      }
    }
  }

  const userSess = getEffectiveSessionForChat(chatId);
  const prof = userSess.profile;
  prof.telegramName = senderName;
  prof.telegramUsername = senderUsername || null;

  // Commands that work even if bot is paused
  if (text.startsWith('/start') || text.startsWith('/status')) {
    awaitingFolderNameChats.delete(chatId);
    awaitingUrlToTelegramChats.delete(chatId);
    awaitingDriveSearchChats.delete(chatId);
    await sendTelegramMessage(chatId, buildControlPanelText(chatId), messageId, buildMainControlKeyboard(chatId));
    return;
  }

  if (text.startsWith('/settings')) {
    awaitingFolderNameChats.delete(chatId);
    await sendTelegramMessage(chatId, buildSettingsPortalText(chatId), messageId, buildSettingsPortalKeyboard(chatId));
    return;
  }

  if (text.startsWith('/admin')) {
    awaitingFolderNameChats.delete(chatId);
    await sendTelegramMessage(chatId, buildAdminPortalText(chatId), messageId, buildAdminPortalKeyboard(chatId));
    return;
  }

  if (text.startsWith('/active')) {
    await sendTelegramMessage(chatId, buildActiveTransfersText(chatId), messageId, buildActiveTransfersKeyboard(chatId));
    return;
  }

  if (text.startsWith('/fromdrive') || text.startsWith('/pull')) {
    if (!userSess.accessToken) {
      await sendTelegramMessage(
        chatId,
        `⚠️ يرجى ربط أو تنشيط حسابك الشخصي في Google Drive أولاً من بوابة الإعدادات.`,
        messageId,
        buildSettingsPortalKeyboard(chatId)
      );
      return;
    }
    try {
      const files = await listDriveFilesForTelegram(userSess.accessToken);
      const rows: any[][] = [];
      for (const f of files.slice(0, 10)) {
        const sizeStr = f.size ? formatBytes(parseInt(f.size, 10)) : 'ملف';
        const shortName = f.name.length > 26 ? f.name.slice(0, 24) + '…' : f.name;
        rows.push([{ text: `📲 ${shortName} (${sizeStr})`, callback_data: `pull_drive_${f.id}` }]);
      }
      rows.push([
        { text: '🔍 بحث عن ملف في Drive', callback_data: 'prompt_search_drive_for_tg' },
        { text: '🏠 القائمة الرئيسية', callback_data: 'open_main' },
      ]);
      await sendTelegramMessage(
        chatId,
        `📥 <b>اختر أي ملف من حسابك الشخصي Google Drive (${userSess.userEmail || 'متصل'}) لسحبه وإرساله إلى تليجرام:</b>`,
        messageId,
        { inline_keyboard: rows }
      );
    } catch (err: any) {
      await sendTelegramMessage(chatId, `⚠️ ${err.message}`, messageId, buildMainControlKeyboard(chatId));
    }
    return;
  }

  if (text.startsWith('/clear')) {
    const removed = clearAllFailedAndCancelledJobs(chatId);
    await sendTelegramMessage(
      chatId,
      `🗑️ تم حذف <b>${removed}</b> من الملفات الفاشلة والملغاة من سجلك بنجاح.`,
      messageId,
      buildMainControlKeyboard(chatId)
    );
    return;
  }

  // Handle interactive search in Google Drive to send to Telegram
  if (awaitingDriveSearchChats.has(chatId) && text && !text.startsWith('/')) {
    awaitingDriveSearchChats.delete(chatId);
    if (!userSess.accessToken) {
      await sendTelegramMessage(
        chatId,
        `⚠️ يرجى ربط حسابك في Google Drive أولاً.`,
        messageId,
        buildSettingsPortalKeyboard(chatId)
      );
      return;
    }
    try {
      const files = await listDriveFilesForTelegram(userSess.accessToken, text);
      if (files.length === 0) {
        await sendTelegramMessage(
          chatId,
          `🔍 لم يتم العثور على ملفات مطابقة لـ <code>${text}</code> في حسابك Google Drive.`,
          messageId,
          {
            inline_keyboard: [
              [
                { text: '🔍 بحث مرة أخرى', callback_data: 'prompt_search_drive_for_tg' },
                { text: '📥 عرض أحدث الملفات', callback_data: 'menu_pull_from_drive' },
              ],
            ],
          }
        );
        return;
      }
      const rows: any[][] = [];
      for (const f of files.slice(0, 10)) {
        const sizeStr = f.size ? formatBytes(parseInt(f.size, 10)) : 'ملف';
        const shortName = f.name.length > 26 ? f.name.slice(0, 24) + '…' : f.name;
        rows.push([{ text: `📲 ${shortName} (${sizeStr})`, callback_data: `pull_drive_${f.id}` }]);
      }
      rows.push([{ text: '🔙 القائمة الرئيسية', callback_data: 'open_main' }]);
      await sendTelegramMessage(
        chatId,
        `🔍 <b>نتائج البحث في حسابك Google Drive عن (<code>${text}</code>):</b>\nاضغط على أي ملف لسحبه وإرساله فوراً إلى تليجرام:`,
        messageId,
        { inline_keyboard: rows }
      );
    } catch (err: any) {
      await sendTelegramMessage(chatId, `⚠️ ${err.message}`, messageId, buildMainControlKeyboard(chatId));
    }
    return;
  }

  // Check if user was prompted to type a new folder name
  if (awaitingFolderNameChats.has(chatId) && text && !text.startsWith('/')) {
    awaitingFolderNameChats.delete(chatId);
    const newFolderName = text.trim();
    prof.activeFolderName = newFolderName;
    prof.activeFolderId = null;
    syncLegacyOwnerGlobalsIfOwner(chatId, prof);
    saveStateToDisk();

    if (userSess.accessToken) {
      try {
        const folder = await ensureDriveFolder(userSess.accessToken, newFolderName);
        prof.activeFolderId = folder.id;
        prof.activeFolderName = folder.name;
        syncLegacyOwnerGlobalsIfOwner(chatId, prof);
        cachedFoldersById.set(folder.id, folder.name);
        saveStateToDisk();
        await sendTelegramMessage(
          chatId,
          `✅ <b>تم إنشاء وتفعيل المجلد الجديد في حسابك بنجاح:</b>\n📁 <code>${folder.name}</code>\n\nسيتم حفظ جميع الملفات القادمة فيه مباشرة.`,
          messageId,
          buildMainControlKeyboard(chatId)
        );
      } catch (err: any) {
        await sendTelegramMessage(
          chatId,
          `⚠️ تم حفظ اسم المجلد (<code>${newFolderName}</code>) ولكن تعذر التحقق من Drive حالياً: ${err.message}`,
          messageId,
          buildMainControlKeyboard(chatId)
        );
      }
    } else {
      await sendTelegramMessage(
        chatId,
        `✅ تم ضبط المجلد النشط لحسابك إلى <code>${newFolderName}</code>. سيتم إنشاؤه تلقائياً عند الاتصال بـ Google Drive.`,
        messageId,
        buildMainControlKeyboard(chatId)
      );
    }
    return;
  }

  if (text.startsWith('/folders')) {
    if (!userSess.accessToken) {
      await sendTelegramMessage(
        chatId,
        `⚠️ يرجى ربط أو تنشيط جلسة حسابك Google Drive أولاً لعرض مجلداتك.`,
        messageId,
        buildSettingsPortalKeyboard(chatId)
      );
      return;
    }
    try {
      const folders = await listDriveFolders(userSess.accessToken);
      const keyboardRows: any[][] = [];
      for (const f of folders.slice(0, 10)) {
        cachedFoldersById.set(f.id, f.name);
        const isCurrent = userSess.activeFolderId === f.id;
        keyboardRows.push([
          {
            text: `${isCurrent ? '✅ ' : '📁 '}${f.name}`,
            callback_data: `setfolder_${f.id}`,
          },
        ]);
      }
      keyboardRows.push([
        { text: '➕ إنشاء مجلد جديد', callback_data: 'prompt_new_folder' },
        { text: '⚙️ بوابة الإعدادات', callback_data: 'portal_settings' },
      ]);
      await sendTelegramMessage(
        chatId,
        `📁 <b>اختر مجلد الحفظ في حسابك Google Drive:</b>\nالمجلد النشط حالياً: <code>${userSess.activeFolderName}</code>`,
        messageId,
        { inline_keyboard: keyboardRows }
      );
    } catch (err: any) {
      await sendTelegramMessage(chatId, `⚠️ ${err.message}`, messageId, buildMainControlKeyboard(chatId));
    }
    return;
  }

  if (text.startsWith('/files')) {
    const userJobs = getJobsForUser(chatId, userSess.userEmail);
    const completed = userJobs.filter((j) => j.status === 'completed').slice(0, 10);
    if (completed.length === 0) {
      await sendTelegramMessage(
        chatId,
        `📄 لا توجد ملفات مرفوعة في سجلك حتى الآن.`,
        messageId,
        buildMainControlKeyboard(chatId)
      );
      return;
    }
    const lines = completed.map(
      (j, idx) =>
        `${idx + 1}. 📄 <a href="${j.webViewLink || '#'}">${j.fileName}</a> — <code>${formatBytes(
          j.bytesTransferred || j.totalBytes
        )}</code>`
    );
    await sendTelegramMessage(
      chatId,
      `📄 <b>آخر ${completed.length} ملفات مرفوعة إلى حسابك Google Drive:</b>\n\n` + lines.join('\n'),
      messageId,
      buildMainControlKeyboard(chatId)
    );
    return;
  }

  if (adminConfig.botPaused) {
    await sendTelegramMessage(
      chatId,
      `⏸️ <b>البوت متوقف مؤقتاً عن استقبال الملفات بأمر المالك.</b>\nيمكنك إعادة تشغيله من <b>🛡️ بوابة الإدارة</b>.`,
      messageId,
      buildMainControlKeyboard(chatId)
    );
    return;
  }

  // Extract file attachment details + file_unique_id for deduplication
  let telegramFileId: string | undefined;
  let telegramFileUniqueId: string | undefined;
  let fileName = '';
  let mimeType = 'application/octet-stream';
  let fileSize = 0;

  if (msg.document) {
    telegramFileId = msg.document.file_id;
    telegramFileUniqueId = msg.document.file_unique_id;
    fileName = msg.document.file_name || `document_${messageId}`;
    mimeType = msg.document.mime_type || 'application/octet-stream';
    fileSize = msg.document.file_size || 0;
  } else if (msg.video) {
    telegramFileId = msg.video.file_id;
    telegramFileUniqueId = msg.video.file_unique_id;
    fileName = msg.video.file_name || `video_${messageId}.mp4`;
    mimeType = msg.video.mime_type || 'video/mp4';
    fileSize = msg.video.file_size || 0;
  } else if (msg.audio) {
    telegramFileId = msg.audio.file_id;
    telegramFileUniqueId = msg.audio.file_unique_id;
    fileName = msg.audio.file_name || `${msg.audio.performer || 'audio'}_${msg.audio.title || messageId}.mp3`;
    mimeType = msg.audio.mime_type || 'audio/mpeg';
    fileSize = msg.audio.file_size || 0;
  } else if (msg.photo && Array.isArray(msg.photo) && msg.photo.length > 0) {
    const largestPhoto = msg.photo[msg.photo.length - 1];
    telegramFileId = largestPhoto.file_id;
    telegramFileUniqueId = largestPhoto.file_unique_id;
    fileName = `photo_${largestPhoto.file_unique_id || messageId}.jpg`;
    mimeType = 'image/jpeg';
    fileSize = largestPhoto.file_size || 0;
  } else if (msg.voice) {
    telegramFileId = msg.voice.file_id;
    telegramFileUniqueId = msg.voice.file_unique_id;
    fileName = `voice_${msg.voice.file_unique_id || messageId}.ogg`;
    mimeType = msg.voice.mime_type || 'audio/ogg';
    fileSize = msg.voice.file_size || 0;
  } else if (msg.video_note) {
    telegramFileId = msg.video_note.file_id;
    telegramFileUniqueId = msg.video_note.file_unique_id;
    fileName = `video_note_${msg.video_note.file_unique_id || messageId}.mp4`;
    mimeType = 'video/mp4';
    fileSize = msg.video_note.file_size || 0;
  } else if (msg.animation) {
    telegramFileId = msg.animation.file_id;
    telegramFileUniqueId = msg.animation.file_unique_id;
    fileName = msg.animation.file_name || `animation_${messageId}.mp4`;
    mimeType = msg.animation.mime_type || 'video/mp4';
    fileSize = msg.animation.file_size || 0;
  } else if (msg.sticker) {
    telegramFileId = msg.sticker.file_id;
    telegramFileUniqueId = msg.sticker.file_unique_id;
    const ext = msg.sticker.is_video ? 'webm' : msg.sticker.is_animated ? 'tgs' : 'webp';
    fileName = `sticker_${msg.sticker.file_unique_id || messageId}.${ext}`;
    mimeType = msg.sticker.is_video ? 'video/webm' : 'image/webp';
    fileSize = msg.sticker.file_size || 0;
  }

  let directUrl: string | undefined;
  const forceToTelegramCmd = text.startsWith('/totg') || awaitingUrlToTelegramChats.has(chatId);
  if (!telegramFileId && text) {
    const urlMatch = text.replace(/^\/(url|totg)\s*/i, '').match(/https?:\/\/[^\s]+/i);
    if (urlMatch) {
      directUrl = urlMatch[0];
      fileName = extractFilenameFromUrl(directUrl);
      awaitingUrlToTelegramChats.delete(chatId);
    }
  }

  if (!telegramFileId && !directUrl) {
    await sendTelegramMessage(
      chatId,
      `💡 أرسل أي <b>ملف</b> أو <b>رابط</b>، أو استخدم البوابات التالية للتحكم الكامل بحسابك:`,
      messageId,
      buildMainControlKeyboard(chatId)
    );
    return;
  }

  if (adminConfig.knownUsers[String(chatId)]) {
    adminConfig.knownUsers[String(chatId)].transfersCount += 1;
  }

  // If the user sent a URL and urlHandlingMode is 'ask' (and not explicitly forced to Telegram)
  if (directUrl && !forceToTelegramCmd && userSess.urlHandlingMode === 'ask') {
    const choiceId = `${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
    pendingUrlChoices.set(choiceId, {
      url: directUrl,
      chatId,
      messageId,
      senderName,
      senderUsername,
      selectedQuality: userSess.defaultQuality || '720',
      compressMode: userSess.defaultCompressMode || 'none',
    });

    const built = buildUrlPromptMessageAndKeyboard(choiceId);
    await sendTelegramMessage(chatId, built.text, messageId, built.replyMarkup);
    return;
  }

  const isUrlToTelegram = Boolean(directUrl && (forceToTelegramCmd || userSess.urlHandlingMode === 'to_telegram'));

  if (isUrlToTelegram && directUrl) {
    const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
    const statusMsgId = await sendTelegramMessage(
      chatId,
      `📥 <b>جاري سحب الرابط وإرساله كملف إلى تليجرام...</b>\n📄 <code>${fileName}</code>`,
      messageId,
      {
        inline_keyboard: [[{ text: '⛔ إلغاء السحب', callback_data: `cancel_${jobId}` }]],
      }
    );

    const job: TransferJob = {
      id: jobId,
      source: 'url_to_telegram',
      direction: 'to_telegram',
      protocol: 'http',
      quality: userSess.defaultQuality || '720',
      compressMode: userSess.defaultCompressMode || 'none',
      fileName,
      mimeType: 'application/octet-stream',
      totalBytes: 0,
      bytesTransferred: 0,
      speedBps: 0,
      status: 'queued',
      senderName,
      senderUsername,
      accountEmail: userSess.userEmail || 'default',
      chatId,
      messageId,
      statusMessageId: statusMsgId,
      directUrl,
      createdAt: new Date().toISOString(),
    };

    transferJobs.unshift(job);
    saveStateToDisk();
    if (IS_VERCEL) await executePullToTelegramJob(job);
    else executePullToTelegramJob(job);
    return;
  }

  // Check if an identical file is currently actively uploading right now
  if (userSess.skipDuplicates) {
    const currentAccount = userSess.userEmail || 'default';
    const activeSameJob = transferJobs.find((j) => {
      if (j.status !== 'downloading' && j.status !== 'uploading' && j.status !== 'queued') return false;
      if (j.accountEmail && j.accountEmail !== currentAccount) return false;
      if (telegramFileUniqueId && j.telegramFileUniqueId === telegramFileUniqueId) return true;
      if (j.fileName === fileName && fileSize > 0 && j.totalBytes === fileSize) return true;
      return false;
    });

    if (activeSameJob) {
      await sendTelegramMessage(
        chatId,
        `⚡ <b>هذا الملف قيد الرفع حالياً بالفعل!</b>\n📄 <code>${fileName}</code>\nتم تخطي النسخة المكررة لمنع التكرار في حسابك.`,
        messageId
      );
      return;
    }
  }

  const canUploadNow = Boolean(userSess.accessToken && userSess.accountEnabled);
  const personalAppUrl = getAppUrl(chatId);
  const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
  const initialStatusText = canUploadNow
    ? `📥 <b>تم استلام الملف وجاري الفحص والتحويل إلى حسابك Google Drive...</b>\n📄 <b>الملف:</b> <code>${fileName}</code>${
        fileSize > 0 ? `\n📦 <b>الحجم:</b> ${formatBytes(fileSize)}` : ''
      }`
    : !userSess.accountEnabled
    ? `⏸️ <b>استقبال حسابك متوقف مؤقتاً في الإعدادات!</b>\n📄 <b>الملف:</b> <code>${fileName}</code>\nتمت إضافته للطابور حتى تعيد تفعيل حسابك من بوابة الإعدادات.`
    : `⏳ <b>تم استلام الملف وإضافته لطابور الانتظار!</b>\n📄 <b>الملف:</b> <code>${fileName}</code>\n🔗 يرجى ربط حسابك الشخصي Google Drive من الزر أدناه أو عبر رمز الربط (<code>${prof.linkCode}</code>) ليبدأ الرفع تلقائياً إلى حسابك.`;

  const cancelMarkupRows: any[][] = [
    [
      { text: '⛔ إلغاء رفع هذا الملف', callback_data: `cancel_${jobId}` },
      { text: '📡 العمليات الجارية', callback_data: 'view_active_transfers' },
    ],
  ];
  if (!userSess.accessToken && personalAppUrl && personalAppUrl.startsWith('https://')) {
    cancelMarkupRows.unshift([{ text: '🔗 ربط حسابي الشخصي Google Drive الآن', url: personalAppUrl }]);
  }

  const statusMsgId = await sendTelegramMessage(chatId, initialStatusText, messageId, {
    inline_keyboard: cancelMarkupRows,
  });

  const job: TransferJob = {
    id: jobId,
    source: telegramFileId ? 'telegram' : 'url',
    direction: 'to_drive',
    quality: userSess.defaultQuality || '720',
    compressMode: userSess.defaultCompressMode || 'none',
    fileName,
    mimeType,
    totalBytes: fileSize,
    bytesTransferred: 0,
    speedBps: 0,
    status: canUploadNow ? 'queued' : 'waiting_auth',
    senderName,
    senderUsername,
    accountEmail: userSess.userEmail || 'default',
    chatId,
    messageId,
    statusMessageId: statusMsgId,
    telegramFileId,
    telegramFileUniqueId,
    directUrl,
    folderName: userSess.activeFolderName,
    createdAt: new Date().toISOString(),
  };

  transferJobs.unshift(job);
  if (transferJobs.length > 200) {
    transferJobs.pop();
  }
  saveStateToDisk();

  if (canUploadNow) {
    if (IS_VERCEL) await executeTransferJob(job);
    else executeTransferJob(job);
  }
}

// ============================================================================
// Long-Polling Daemon + Bot Menu Registration + MTProto Startup
// ============================================================================

async function startTelegramServices(): Promise<void> {
  const token = getBotToken();
  if (!token) {
    botInfo = null;
    botConnectionError = 'لم يتم العثور على TELEGRAM_BOT_TOKEN في قسم الأسرار (Secrets) بعد.';
    isPolling = false;
    return;
  }

  if (isPolling && pollingAbortController) {
    pollingAbortController.abort();
    isPolling = false;
  }

  startMtprotoEngine()
    .then(() => {
      // Automatically resume any interrupted active transfers with the new Turbo Engine
      const interrupted = transferJobs.filter(
        (j) => j.status === 'uploading' || j.status === 'downloading' || j.status === 'queued'
      );
      for (const job of interrupted) {
        if (!jobAbortControllers.has(job.id)) {
          if (job.direction === 'to_telegram' || job.source === 'drive_to_telegram' || job.source === 'url_to_telegram') {
            executePullToTelegramJob(job);
          } else if (driveSession.accessToken && adminConfig.accountEnabled) {
            executeTransferJob(job);
          }
        }
      }
    })
    .catch((err) => console.warn('MTProto startup error:', err));

  try {
    const me = await telegramApi<BotInfo>('getMe');
    botInfo = me;
    botConnectionError = null;

    await telegramApi('setMyCommands', {
      commands: [
        { command: 'start', description: '🏠 القائمة الرئيسية وجميع البوابات' },
        { command: 'settings', description: '⚙️ بوابة الإعدادات وربط/إلغاء ربط الحساب' },
        { command: 'admin', description: '🛡️ بوابة الإدارة والتحكم لمالك الموقع' },
        { command: 'active', description: '📡 إظهار عمليات الرفع الحالية وإلغاؤها' },
        { command: 'fromdrive', description: '📥 سحب ملف من Google Drive إلى تليجرام' },
        { command: 'folders', description: '📁 اختيار أو إنشاء مجلد في Google Drive' },
        { command: 'clear', description: '🗑️ حذف جميع الملفات الفاشلة والملغاة' },
      ],
    }).catch((err) => console.warn('setMyCommands warning:', err));

    // On Vercel Serverless, use Telegram Webhook mode instead of an infinite Long-Polling loop
    if (IS_VERCEL || process.env.TELEGRAM_MODE === 'webhook') {
      const baseUrl = getAppUrl();
      if (baseUrl && baseUrl.startsWith('https://')) {
        const webhookTarget = `${baseUrl}/api/telegram/webhook`;
        await telegramApi('setWebhook', {
          url: webhookTarget,
          allowed_updates: ['message', 'channel_post', 'callback_query'],
          drop_pending_updates: false,
        });
        isWebhookRegistered = true;
        activeWebhookUrl = webhookTarget;
        console.log(`Telegram Bot Webhook registered for Vercel: ${webhookTarget}`);
      } else {
        isWebhookRegistered = true;
      }
      isPolling = false;
      return;
    }

    await telegramApi('deleteWebhook', { drop_pending_updates: false });
    isWebhookRegistered = false;
    activeWebhookUrl = null;

    isPolling = true;
    pollingAbortController = new AbortController();
    const currentSignal = pollingAbortController.signal;

    console.log(`Telegram Bot connected: @${me.username} (${me.first_name})`);

    (async () => {
      while (isPolling && !currentSignal.aborted) {
        try {
          const updates = await telegramApi<any[]>(
            'getUpdates',
            {
              offset: lastUpdateId + 1,
              timeout: 25,
              allowed_updates: ['message', 'channel_post', 'callback_query'],
            },
            currentSignal
          );

          for (const update of updates) {
            if (update.update_id > lastUpdateId) {
              lastUpdateId = update.update_id;
            }
            handleTelegramUpdate(update).catch((err) => {
              console.warn('Error handling Telegram update:', err);
            });
          }
        } catch (err: any) {
          if (currentSignal.aborted) break;
          await new Promise((r) => setTimeout(r, 3000));
        }
      }
    })();
  } catch (err: any) {
    botInfo = null;
    botConnectionError = err?.message || 'تعذر الاتصال ببوت تليجرام. تأكد من صحة TELEGRAM_BOT_TOKEN.';
    isPolling = false;
  }
}

startTelegramServices();

// Capture incoming request origin for automatic Vercel URL & Webhook resolution
app.use((req, _res, next) => {
  const host = (req.headers['x-forwarded-host'] as string) || req.headers.host || '';
  const proto = (req.headers['x-forwarded-proto'] as string) || 'https';
  if (host && !host.startsWith('localhost') && !host.startsWith('127.0.0.1')) {
    const cleanHost = host.split(',')[0].trim();
    const cleanProto = proto.split(',')[0].trim() || 'https';
    lastDetectedOrigin = `${cleanProto}://${cleanHost}`;
    if (IS_VERCEL && getBotToken() && !activeWebhookUrl && lastDetectedOrigin.startsWith('https://')) {
      const target = `${lastDetectedOrigin}/api/telegram/webhook`;
      activeWebhookUrl = target;
      isWebhookRegistered = true;
      telegramApi('setWebhook', {
        url: target,
        allowed_updates: ['message', 'channel_post', 'callback_query'],
        drop_pending_updates: false,
      }).catch(() => {});
    }
  }
  next();
});

// ============================================================================
// Express API Routes (Multi-User Personal Account & Session Scoping)
// ============================================================================

function resolveRequestUserContext(req: express.Request): {
  userEmail: string | null;
  chatId: number | null;
  profile: UserDriveProfile;
  session: ReturnType<typeof getEffectiveSessionForChat>;
} {
  const rawEmail =
    (typeof req.query.userEmail === 'string' && req.query.userEmail) ||
    (typeof req.headers['x-user-email'] === 'string' && req.headers['x-user-email']) ||
    (req.body && typeof req.body.userEmail === 'string' && req.body.userEmail) ||
    '';
  const cleanEmail = rawEmail.trim() || null;

  const rawChatId =
    (typeof req.query.chatId === 'string' && req.query.chatId) ||
    (typeof req.headers['x-chat-id'] === 'string' && req.headers['x-chat-id']) ||
    (req.body && (req.body.chatId || req.body.targetChatId)) ||
    '';
  const parsedChatId = Number(rawChatId);
  const validChatId = !isNaN(parsedChatId) && parsedChatId !== 0 ? parsedChatId : null;

  if (cleanEmail && userProfiles[cleanEmail]) {
    const prof = userProfiles[cleanEmail];
    if (validChatId && !prof.chatId) {
      prof.chatId = validChatId;
    }
    return {
      userEmail: prof.userEmail,
      chatId: prof.chatId || validChatId,
      profile: prof,
      session: {
        accessToken: prof.accessToken,
        userEmail: prof.userEmail,
        userName: prof.userName,
        activeFolderId: prof.activeFolderId,
        activeFolderName: prof.activeFolderName || 'Telegram Bot Uploads',
        accountEnabled: prof.accountEnabled,
        autoCategorizeByType: prof.autoCategorizeByType,
        skipDuplicates: prof.skipDuplicates,
        urlHandlingMode: prof.urlHandlingMode,
        defaultQuality: prof.defaultQuality || '720',
        defaultCompressMode: prof.defaultCompressMode || 'none',
        profile: prof,
      },
    };
  }

  if (validChatId) {
    const sess = getEffectiveSessionForChat(validChatId);
    return {
      userEmail: sess.userEmail,
      chatId: validChatId,
      profile: sess.profile,
      session: sess,
    };
  }

  if (cleanEmail) {
    const prof = getOrCreateUserProfile({ email: cleanEmail });
    return {
      userEmail: prof.userEmail,
      chatId: prof.chatId,
      profile: prof,
      session: {
        accessToken: prof.accessToken,
        userEmail: prof.userEmail,
        userName: prof.userName,
        activeFolderId: prof.activeFolderId,
        activeFolderName: prof.activeFolderName || 'Telegram Bot Uploads',
        accountEnabled: prof.accountEnabled,
        autoCategorizeByType: prof.autoCategorizeByType,
        skipDuplicates: prof.skipDuplicates,
        urlHandlingMode: prof.urlHandlingMode,
        defaultQuality: prof.defaultQuality || '720',
        defaultCompressMode: prof.defaultCompressMode || 'none',
        profile: prof,
      },
    };
  }

  const fallbackSess = getEffectiveSessionForChat(undefined);
  return {
    userEmail: fallbackSess.userEmail,
    chatId: fallbackSess.profile.chatId || adminConfig.ownerChatId,
    profile: fallbackSess.profile,
    session: fallbackSess,
  };
}

app.post('/api/telegram/webhook', async (req, res) => {
  const update = req.body;
  if (update) {
    try {
      await handleTelegramUpdate(update);
    } catch (err) {
      console.warn('Webhook update error:', err);
    }
  }
  res.status(200).json({ ok: true });
});

app.post('/api/bot/webhook', async (req, res) => {
  if (!getBotToken()) {
    res.status(400).json({ error: 'يرجى إضافة TELEGRAM_BOT_TOKEN في متغيرات البيئة (Environment Variables) أولاً.' });
    return;
  }
  const customOrigin = typeof req.body?.origin === 'string' ? req.body.origin.trim().replace(/\/+$/, '') : '';
  const baseUrl = customOrigin || getAppUrl();
  if (!baseUrl || !baseUrl.startsWith('https://')) {
    res.status(400).json({ error: 'يتطلب تليجرام رابط HTTPS صالح لتفعيل الـ Webhook.' });
    return;
  }
  try {
    if (isPolling && pollingAbortController) {
      pollingAbortController.abort();
      isPolling = false;
    }
    const me = await telegramApi<BotInfo>('getMe');
    botInfo = me;
    botConnectionError = null;
    const webhookTarget = `${baseUrl}/api/telegram/webhook`;
    await telegramApi('setWebhook', {
      url: webhookTarget,
      allowed_updates: ['message', 'channel_post', 'callback_query'],
      drop_pending_updates: false,
    });
    isWebhookRegistered = true;
    activeWebhookUrl = webhookTarget;
    res.json({
      ok: true,
      mode: 'webhook',
      webhookUrl: webhookTarget,
      bot: botInfo,
    });
  } catch (err: any) {
    res.status(500).json({ error: err?.message || 'فشل تسجيل Webhook لدى تليجرام.' });
  }
});

app.get('/api/status', async (req, res) => {
  const hasToken = Boolean(getBotToken());
  if (hasToken && !botInfo) {
    try {
      await startTelegramServices();
    } catch {
      // Ignore cold-start error
    }
  }
  const hasMtprotoConfig = Boolean(getApiId() && getApiHash());
  const ctx = resolveRequestUserContext(req);
  const { profile, session } = ctx;

  // Scope jobs to the current user unless they explicitly have no personal identity yet
  const hasPersonalIdentity = Boolean(ctx.userEmail || ctx.chatId);
  const scopedJobs = hasPersonalIdentity
    ? getJobsForUser(ctx.chatId || undefined, ctx.userEmail)
    : getJobsForUser(adminConfig.ownerChatId || undefined, driveSession.userEmail);

  const completedScoped = scopedJobs.filter((j) => j.status === 'completed');
  const totalBytesScoped = completedScoped.reduce((acc, j) => acc + (j.bytesTransferred || j.totalBytes || 0), 0);

  const globalCompleted = transferJobs.filter((j) => j.status === 'completed');
  const globalTotalBytes = globalCompleted.reduce((acc, j) => acc + (j.bytesTransferred || j.totalBytes || 0), 0);

  const enrichedKnownUsers = Object.values(adminConfig.knownUsers).map((u) => {
    const uSess = getEffectiveSessionForChat(u.chatId);
    return {
      ...u,
      linkedEmail: uSess.userEmail || null,
      driveConnected: Boolean(uSess.accessToken),
    };
  });

  res.json({
    deployment: {
      isVercel: IS_VERCEL,
      mode: isWebhookRegistered || IS_VERCEL ? 'webhook' : 'polling',
      webhookUrl: activeWebhookUrl,
      appUrl: getAppUrl(),
    },
    bot: {
      configured: hasToken,
      connected: Boolean(botInfo && (isPolling || isWebhookRegistered || IS_VERCEL)),
      info: botInfo,
      error: botConnectionError,
      apiRoot: getTelegramApiRoot(),
      isCustomApiRoot: getTelegramApiRoot() !== 'https://api.telegram.org',
      mtproto: {
        configured: hasMtprotoConfig,
        connected: mtprotoConnected,
        error: mtprotoError,
        maxFileSizeLabel: mtprotoConnected ? '2,000 MB (2 GB)' : '20 MB (قياسي)',
      },
    },
    drive: {
      connected: Boolean(session.accessToken),
      activeAccessToken: session.accessToken || null,
      accountEnabled: session.accountEnabled,
      userEmail: session.userEmail,
      userName: session.userName,
      activeFolderId: session.activeFolderId,
      activeFolderName: session.activeFolderName,
      autoCategorizeByType: session.autoCategorizeByType,
      skipDuplicates: session.skipDuplicates,
      urlHandlingMode: session.urlHandlingMode,
      defaultQuality: session.defaultQuality || '720',
      defaultCompressMode: session.defaultCompressMode || 'none',
      lastSyncedAt: profile.lastSyncedAt || driveSession.lastSyncedAt,
      linkCode: profile.linkCode,
      linkedChatId: profile.chatId || null,
      linkedTelegramName: profile.telegramName || null,
      linkedTelegramUsername: profile.telegramUsername || null,
    },
    admin: {
      ownerChatId: adminConfig.ownerChatId,
      ownerName: adminConfig.ownerName,
      ownerUsername: adminConfig.ownerUsername,
      accessMode: adminConfig.accessMode,
      botPaused: adminConfig.botPaused,
      knownUsers: enrichedKnownUsers,
      connectedProfilesCount: Object.values(userProfiles).filter((p) => Boolean(p.accessToken)).length,
      globalStats: {
        totalJobs: transferJobs.length,
        completedJobs: globalCompleted.length,
        activeJobs: transferJobs.filter((j) => j.status === 'downloading' || j.status === 'uploading').length,
        waitingAuthJobs: transferJobs.filter((j) => j.status === 'waiting_auth' || j.status === 'queued').length,
        failedJobs: transferJobs.filter((j) => j.status === 'failed' || j.status === 'cancelled').length,
        totalBytesTransferred: globalTotalBytes,
      },
      globalActiveJobs: transferJobs
        .filter((j) => j.status === 'downloading' || j.status === 'uploading' || j.status === 'queued')
        .slice(0, 30),
    },
    stats: {
      totalJobs: scopedJobs.length,
      completedJobs: completedScoped.length,
      activeJobs: scopedJobs.filter((j) => j.status === 'downloading' || j.status === 'uploading').length,
      waitingAuthJobs: scopedJobs.filter((j) => j.status === 'waiting_auth' || j.status === 'queued').length,
      failedJobs: scopedJobs.filter((j) => j.status === 'failed' || j.status === 'cancelled').length,
      totalBytesTransferred: totalBytesScoped,
    },
    jobs: scopedJobs.slice(0, 100),
  });
});

app.post('/api/bot/reconnect', async (_req, res) => {
  dotenv.config({ override: true });
  await startTelegramServices();
  res.json({
    configured: Boolean(getBotToken()),
    connected: Boolean(botInfo && isPolling),
    info: botInfo,
    error: botConnectionError,
    mtproto: {
      configured: Boolean(getApiId() && getApiHash()),
      connected: mtprotoConnected,
      error: mtprotoError,
    },
  });
});

app.post('/api/drive/sync', async (req, res) => {
  const authHeader = req.headers.authorization;
  if (!authHeader || !authHeader.startsWith('Bearer ')) {
    res.status(401).json({ error: 'مطلوب رمز مصادقة Google Drive.' });
    return;
  }

  const token = authHeader.replace('Bearer ', '').trim();
  const {
    userEmail,
    userName,
    chatId,
    folderName,
    folderId,
    autoCategorize,
    deduplicate,
    accountEnabled,
    urlHandlingMode,
  } = req.body || {};

  const parsedChatId = Number(chatId);
  const validChatId = !isNaN(parsedChatId) && parsedChatId !== 0 ? parsedChatId : undefined;
  const cleanEmail = typeof userEmail === 'string' && userEmail.trim() ? userEmail.trim() : undefined;

  const prof = getOrCreateUserProfile({ email: cleanEmail, chatId: validChatId });
  const wasUnlinkedOrDifferentEmail = !prof.accessToken || (cleanEmail && prof.userEmail !== cleanEmail);

  prof.accessToken = token;
  if (cleanEmail) prof.userEmail = cleanEmail;
  if (userName !== undefined) prof.userName = userName;
  if (validChatId) {
    prof.chatId = validChatId;
    const known = adminConfig.knownUsers[String(validChatId)];
    if (known) {
      prof.telegramName = known.name;
      prof.telegramUsername = known.username || null;
    }
  }
  if (typeof autoCategorize === 'boolean') {
    prof.autoCategorizeByType = autoCategorize;
  }
  if (typeof deduplicate === 'boolean') {
    prof.skipDuplicates = deduplicate;
  }
  if (typeof accountEnabled === 'boolean') {
    prof.accountEnabled = accountEnabled;
  }
  if (urlHandlingMode === 'ask' || urlHandlingMode === 'to_drive' || urlHandlingMode === 'to_telegram') {
    prof.urlHandlingMode = urlHandlingMode;
  }
  prof.lastSyncedAt = new Date().toISOString();

  // Re-key profile under email if it was previously keyed under tg_<chatId>
  if (cleanEmail && !userProfiles[cleanEmail]) {
    userProfiles[cleanEmail] = prof;
  }

  try {
    if (folderId && folderName) {
      prof.activeFolderId = folderId;
      prof.activeFolderName = folderName;
    } else {
      const targetName = folderName || prof.activeFolderName || 'Telegram Bot Uploads';
      const folder = await ensureDriveFolder(token, targetName);
      prof.activeFolderId = folder.id;
      prof.activeFolderName = folder.name;
    }

    // Update legacy owner globals if this user is the owner or no owner is set yet
    if (!adminConfig.ownerChatId || !driveSession.accessToken || prof.chatId === adminConfig.ownerChatId) {
      driveSession.accessToken = prof.accessToken;
      driveSession.userEmail = prof.userEmail;
      driveSession.userName = prof.userName;
      driveSession.activeFolderId = prof.activeFolderId;
      driveSession.activeFolderName = prof.activeFolderName;
      driveSession.lastSyncedAt = prof.lastSyncedAt;
      autoCategorizeByType = prof.autoCategorizeByType;
      skipDuplicates = prof.skipDuplicates;
      adminConfig.accountEnabled = prof.accountEnabled;
      adminConfig.urlHandlingMode = prof.urlHandlingMode;
    }

    // Attribute any waiting jobs from this chatId to this Google account
    if (prof.chatId && prof.userEmail) {
      for (const j of transferJobs) {
        if (j.chatId === prof.chatId && (!j.accountEmail || j.accountEmail === 'default')) {
          j.accountEmail = prof.userEmail;
        }
      }
    }

    saveStateToDisk();
    processPendingQueue(prof.chatId || undefined, prof.userEmail || undefined).catch((err) =>
      console.warn('Queue processing warning:', err)
    );

    if (validChatId && wasUnlinkedOrDifferentEmail) {
      sendTelegramMessage(
        validChatId,
        `✅ <b>تم ربط وتنشيط حسابك الشخصي في Google Drive من الموقع بنجاح!</b>\n\n` +
          `📧 <b>الحساب:</b> <code>${prof.userEmail || 'متصل'}</code>\n` +
          `📁 <b>المجلد النشط:</b> <code>${prof.activeFolderName}</code>\n` +
          `🚀 سيتم الآن رفع جميع ملفاتك مباشرة إلى حسابك الشخصي!`,
        undefined,
        buildMainControlKeyboard(validChatId)
      ).catch(() => {});
    }

    res.json({
      ok: true,
      userEmail: prof.userEmail,
      userName: prof.userName,
      activeFolderId: prof.activeFolderId,
      activeFolderName: prof.activeFolderName,
      autoCategorizeByType: prof.autoCategorizeByType,
      skipDuplicates: prof.skipDuplicates,
      accountEnabled: prof.accountEnabled,
      urlHandlingMode: prof.urlHandlingMode,
      linkCode: prof.linkCode,
      linkedChatId: prof.chatId || null,
    });
  } catch (err: any) {
    res.status(400).json({ error: err?.message || 'تعذر مزامنة مجلد Google Drive.' });
  }
});

app.post('/api/drive/disconnect', (req, res) => {
  const ctx = resolveRequestUserContext(req);
  ctx.profile.accessToken = null;
  if (!adminConfig.ownerChatId || ctx.chatId === adminConfig.ownerChatId || ctx.userEmail === driveSession.userEmail) {
    driveSession.accessToken = null;
    driveSession.userEmail = null;
    driveSession.userName = null;
  }
  saveStateToDisk();
  res.json({ ok: true });
});

// Export active Google Drive session as a portable token for instant Vercel linking
app.get('/api/drive/export-session', (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const authHeader = req.headers.authorization;
  const headerToken =
    authHeader && authHeader.startsWith('Bearer ') ? authHeader.replace('Bearer ', '').trim() : '';
  const token = headerToken || ctx.session.accessToken || driveSession.accessToken;
  if (!token) {
    res.status(400).json({ error: 'لا توجد جلسة Google Drive نشطة حالياً لتصديرها.' });
    return;
  }

  const payload = {
    t: token,
    e: ctx.session.userEmail || driveSession.userEmail || '',
    n: ctx.session.userName || driveSession.userName || 'مستخدم Google Drive',
    c: ctx.chatId || adminConfig.ownerChatId || '',
    fid: ctx.session.activeFolderId || driveSession.activeFolderId || '',
    fn: ctx.session.activeFolderName || driveSession.activeFolderName || 'Telegram Bot Uploads',
  };
  const sessionCode = `TD1_${Buffer.from(JSON.stringify(payload), 'utf8').toString('base64url')}`;
  res.json({
    ok: true,
    sessionCode,
    accessToken: payload.t,
    userEmail: payload.e,
    userName: payload.n,
    chatId: payload.c,
    activeFolderId: payload.fid,
    activeFolderName: payload.fn,
  });
});

// Push active Google Drive session & Telegram webhook directly to a Vercel deployment URL
app.post('/api/vercel/push-session', async (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const authHeader = req.headers.authorization;
  const headerToken =
    authHeader && authHeader.startsWith('Bearer ') ? authHeader.replace('Bearer ', '').trim() : '';

  const { vercelUrl, accessToken, userEmail, userName, chatId, sendToTelegram } = req.body || {};
  const token = accessToken || headerToken || ctx.session.accessToken || driveSession.accessToken;
  if (!token) {
    res.status(400).json({
      error: 'يرجى تسجيل الدخول بحسابك في Google Drive هنا أولاً قبل نقل الجلسة إلى Vercel.',
    });
    return;
  }

  let cleanOrigin = typeof vercelUrl === 'string' ? vercelUrl.trim().replace(/\/+$/, '') : '';
  if (cleanOrigin) {
    if (cleanOrigin.toUpperCase().startsWith('TD1_') || cleanOrigin.includes('magicAuth=')) {
      res.status(400).json({
        error: 'القيمة المدخلة في خانة الرابط تبدو ككود جلسة (TD1_...) وليست رابط موقع. يرجى إدخال رابط موقع Vercel (مثال: https://your-app.vercel.app)',
      });
      return;
    }
    if (!/^https?:\/\//i.test(cleanOrigin)) {
      cleanOrigin = `https://${cleanOrigin}`;
    }
    try {
      const parsed = new URL(cleanOrigin);
      if (!parsed.hostname.includes('.') || parsed.hostname.includes('_')) {
        throw new Error('Invalid hostname');
      }
      cleanOrigin = parsed.origin;
    } catch {
      res.status(400).json({ error: 'يرجى إدخال رابط Vercel صالح (مثال: https://your-app.vercel.app).' });
      return;
    }
  }

  const payload = {
    t: token,
    e: userEmail || ctx.session.userEmail || driveSession.userEmail || '',
    n: userName || ctx.session.userName || driveSession.userName || 'مستخدم Google Drive',
    c: chatId || ctx.chatId || adminConfig.ownerChatId || '',
    fid: ctx.session.activeFolderId || driveSession.activeFolderId || '',
    fn: ctx.session.activeFolderName || driveSession.activeFolderName || 'Telegram Bot Uploads',
  };
  const sessionCode = `TD1_${Buffer.from(JSON.stringify(payload), 'utf8').toString('base64url')}`;
  const magicLoginUrl = cleanOrigin ? `${cleanOrigin}/?magicAuth=${encodeURIComponent(sessionCode)}` : '';

  let remoteSynced = false;
  let webhookSynced = false;
  let remoteError = '';

  if (cleanOrigin) {
    try {
      const syncRes = await fetch(`${cleanOrigin}/api/drive/sync`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          Authorization: `Bearer ${token}`,
        },
        body: JSON.stringify({
          userEmail: payload.e,
          userName: payload.n,
          chatId: payload.c || undefined,
          folderId: payload.fid || undefined,
          folderName: payload.fn,
        }),
        signal: AbortSignal.timeout(12000),
      });
      remoteSynced = syncRes.ok;
      if (!syncRes.ok) {
        const errData = await syncRes.json().catch(() => ({}));
        remoteError = errData?.error || `HTTP ${syncRes.status}`;
      }
    } catch (err: any) {
      remoteError = err?.message || 'تعذر الاتصال بخادم Vercel';
    }

    try {
      const whRes = await fetch(`${cleanOrigin}/api/bot/webhook`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ origin: cleanOrigin }),
        signal: AbortSignal.timeout(10000),
      });
      webhookSynced = whRes.ok;
    } catch {
      // Ignore optional webhook error
    }
  }

  const targetChat = Number(payload.c) || adminConfig.ownerChatId;
  if (sendToTelegram !== false && targetChat) {
    const msgLines = [
      `🌐 <b>تم تجهيز ربط حسابك الشخصي (${payload.e || payload.n}) لمنصة Vercel بنجاح!</b>`,
      ``,
      cleanOrigin
        ? `✅ <b>حالة المزامنة المباشرة مع موقعك:</b> ${
            remoteSynced ? 'تم ربط حسابك على خادم Vercel بنجاح!' : 'استخدم الرابط أو الكود بالأسفل'
          }`
        : '',
      `🔑 <b>كود التفعيل السريع (اضغط لنسخه ولصقه في موقع Vercel):</b>`,
      `<code>${sessionCode}</code>`,
    ].filter(Boolean);

    const inlineKeyboard: any[][] = [];
    if (magicLoginUrl) {
      try {
        const testUrl = new URL(magicLoginUrl);
        if (
          (testUrl.protocol === 'https:' || testUrl.protocol === 'http:') &&
          testUrl.hostname.includes('.') &&
          !testUrl.hostname.includes('_')
        ) {
          inlineKeyboard.push([
            {
              text: '🚀 فتح موقعك على Vercel بالحساب المربوط جاهزاً',
              url: magicLoginUrl,
            },
          ]);
        }
      } catch {
        // Skip invalid button url
      }
    }
    try {
      await sendTelegramMessage(
        targetChat,
        msgLines.join('\n'),
        undefined,
        inlineKeyboard.length > 0 ? { inline_keyboard: inlineKeyboard } : undefined
      );
    } catch (tgErr: any) {
      console.warn('Telegram session message send failed:', tgErr?.message);
    }
  }

  res.json({
    ok: true,
    remoteSynced,
    webhookSynced,
    remoteError: remoteError || null,
    sessionCode,
    magicLoginUrl: magicLoginUrl || null,
    userEmail: payload.e,
  });
});

// Admin & Personal Settings Portal API Endpoint
app.post('/api/admin/settings', (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const prof = ctx.profile;

  const {
    accountEnabled,
    autoCategorize,
    deduplicate,
    urlHandlingMode,
    defaultQuality,
    defaultCompressMode,
    unlinkTelegramChat,
    accessMode,
    botPaused,
    ownerChatId,
    toggleBlockChatId,
    clearAllHistory,
  } = req.body || {};

  if (typeof accountEnabled === 'boolean') {
    prof.accountEnabled = accountEnabled;
    if (accountEnabled && prof.accessToken) {
      processPendingQueue(prof.chatId || undefined, prof.userEmail || undefined).catch(() => {});
    }
  }
  if (typeof autoCategorize === 'boolean') {
    prof.autoCategorizeByType = autoCategorize;
  }
  if (typeof deduplicate === 'boolean') {
    prof.skipDuplicates = deduplicate;
  }
  if (urlHandlingMode === 'ask' || urlHandlingMode === 'to_drive' || urlHandlingMode === 'to_telegram') {
    prof.urlHandlingMode = urlHandlingMode;
  }
  if (typeof defaultQuality === 'string' && defaultQuality.trim()) {
    prof.defaultQuality = defaultQuality.trim();
  }
  if (defaultCompressMode === 'none' || defaultCompressMode === 'zip' || defaultCompressMode === 'media') {
    prof.defaultCompressMode = defaultCompressMode;
  }
  if (unlinkTelegramChat === true) {
    prof.chatId = null;
    prof.telegramName = null;
    prof.telegramUsername = null;
    prof.linkCode = generateLinkCode();
  }

  if (!adminConfig.ownerChatId || prof.chatId === adminConfig.ownerChatId || prof.userEmail === driveSession.userEmail) {
    adminConfig.accountEnabled = prof.accountEnabled;
    autoCategorizeByType = prof.autoCategorizeByType;
    skipDuplicates = prof.skipDuplicates;
    adminConfig.urlHandlingMode = prof.urlHandlingMode;
    adminConfig.defaultQuality = prof.defaultQuality;
    adminConfig.defaultCompressMode = prof.defaultCompressMode;
  }

  if (accessMode === 'public' || accessMode === 'owner_only') {
    adminConfig.accessMode = accessMode;
  }
  if (typeof botPaused === 'boolean') {
    adminConfig.botPaused = botPaused;
  }
  if (ownerChatId !== undefined) {
    const parsed = Number(ownerChatId);
    adminConfig.ownerChatId = !isNaN(parsed) && parsed !== 0 ? parsed : null;
  }
  if (toggleBlockChatId !== undefined) {
    const u = adminConfig.knownUsers[String(toggleBlockChatId)];
    if (u) {
      u.blocked = !u.blocked;
    }
  }
  if (clearAllHistory === true) {
    const active = getActiveJobsList();
    for (const j of active) {
      cancelTransferJobById(j.id);
    }
    transferJobs.length = 0;
  }

  saveStateToDisk();
  res.json({ ok: true, admin: adminConfig, drive: prof });
});

// Resolve Direct Browser Download via JSON (Prevents direct-download.html & records job in history)
app.post('/api/transfers/resolve-direct', async (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const authHeader = req.headers.authorization;
  if (authHeader && authHeader.startsWith('Bearer ')) {
    ctx.profile.accessToken = authHeader.replace('Bearer ', '').trim();
  }

  const { url, customFileName, mediaFormat, quality, compressMode } = req.body || {};
  const cleanUrl = extractCleanHttpUrl(typeof url === 'string' ? url : '');
  if (!cleanUrl || !/^https?:\/\//i.test(cleanUrl)) {
    res.status(400).json({ error: 'يرجى إدخال رابط صالح يبدأ بـ http:// أو https://' });
    return;
  }

  const resolvedFormat: 'video' | 'audio' = mediaFormat === 'audio' ? 'audio' : 'video';
  const resolvedQuality =
    typeof quality === 'string' && quality.trim() ? quality.trim() : ctx.session.defaultQuality || '720';
  const resolvedCompress: CompressMode =
    compressMode === 'zip' || compressMode === 'media' || compressMode === 'none'
      ? compressMode
      : 'none';

  try {
    const resolved = await resolveTelegramPostLinkIfApplicable(cleanUrl, resolvedFormat, resolvedQuality);
    let fileName = (typeof customFileName === 'string' ? customFileName.trim() : '') || '';
    if (!fileName) {
      fileName = resolved.detectedFileName || extractFilenameFromUrl(cleanUrl, resolvedFormat);
    } else if (!fileName.includes('.')) {
      const extMatch = (resolved.detectedFileName || '').match(/(\.[^.]+)$/);
      fileName += extMatch ? extMatch[1] : resolvedFormat === 'audio' ? '.mp3' : '.mp4';
    }

    let mimeType =
      resolved.detectedMimeType || (resolvedFormat === 'audio' ? 'audio/mpeg' : 'video/mp4');
    let totalBytes = 0;

    // Probe the resolved stream to verify it is not an HTML error page and obtain its size
    const probeController = new AbortController();
    const probeTimeout = setTimeout(() => probeController.abort(), 12000);
    try {
      const probeRes = await fetch(resolved.resolvedUrl, {
        method: 'GET',
        headers: {
          Range: 'bytes=0-0',
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
          ...(resolved.customHeaders || {}),
        },
        signal: probeController.signal,
      });

      const ct = (probeRes.headers.get('content-type') || '').toLowerCase();
      if (!probeRes.ok && probeRes.status !== 206) {
        await probeRes.body?.cancel().catch(() => {});
        throw new Error(`المصدر رفض التحميل (${probeRes.status}).`);
      }
      if (ct.includes('text/html') && !fileName.toLowerCase().endsWith('.html')) {
        await probeRes.body?.cancel().catch(() => {});
        throw new Error('المصدر أعاد صفحة HTML بدلاً من ملف الفيديو أو الصوت.');
      }

      const contentRange = probeRes.headers.get('content-range');
      const contentLen = probeRes.headers.get('content-length');
      if (contentRange && contentRange.includes('/')) {
        const totalPart = parseInt(contentRange.split('/')[1], 10);
        if (!isNaN(totalPart) && totalPart > 0) totalBytes = totalPart;
      } else if (contentLen) {
        const parsedLen = parseInt(contentLen, 10);
        if (!isNaN(parsedLen) && parsedLen > 1) totalBytes = parsedLen;
      }

      if (ct && !ct.includes('application/octet-stream')) {
        mimeType = ct.split(';')[0].trim();
      }
      await probeRes.body?.cancel().catch(() => {});
    } finally {
      clearTimeout(probeTimeout);
    }

    const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
    const job: TransferJob = {
      id: jobId,
      source: 'url',
      direction: 'to_device',
      protocol: 'http',
      mediaFormat: resolvedFormat,
      quality: resolvedQuality,
      compressMode: resolvedCompress,
      fileName,
      mimeType,
      totalBytes,
      bytesTransferred: totalBytes,
      speedBps: 0,
      status: 'completed',
      senderName: ctx.session.userName || 'تحميل مباشر للجهاز',
      accountEmail: ctx.session.userEmail || 'default',
      chatId: ctx.chatId || undefined,
      directUrl: resolved.resolvedUrl,
      createdAt: new Date().toISOString(),
      completedAt: new Date().toISOString(),
    };

    transferJobs.unshift(job);
    saveStateToDisk();

    const safePathName = encodeURIComponent(fileName);
    const proxyParams = new URLSearchParams({
      jobId: job.id,
      format: resolvedFormat,
      quality: resolvedQuality,
      compress: resolvedCompress,
      name: fileName,
    });
    if (ctx.userEmail) proxyParams.set('userEmail', ctx.userEmail);
    if (ctx.chatId) proxyParams.set('chatId', String(ctx.chatId));
    const proxyDownloadUrl = `/api/direct-download/${safePathName}?${proxyParams.toString()}`;

    const isDirectAttachmentCdn =
      resolvedCompress === 'none' &&
      /^https:\/\//i.test(resolved.resolvedUrl) &&
      (resolved.resolvedUrl.includes('savetube') ||
        resolved.resolvedUrl.endsWith('.mp4') ||
        resolved.resolvedUrl.endsWith('.mp3'));

    res.json({
      ok: true,
      fileName,
      mimeType,
      totalBytes,
      directStreamUrl: resolved.resolvedUrl,
      preferDirectCdn: isDirectAttachmentCdn,
      proxyDownloadUrl,
      job,
    });
  } catch (err: any) {
    res.status(400).json({
      error: err?.message || 'تعذر استخراج رابط التحميل المباشر للفيديو أو الصوت.',
    });
  }
});

// Direct Browser Download Endpoint (Download Video, Audio, or File Directly to Device)
app.get(['/api/direct-download', '/api/direct-download/:pathFileName'], async (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const rawUrl = typeof req.query.url === 'string' ? extractCleanHttpUrl(req.query.url) : '';
  const driveFileId = typeof req.query.driveFileId === 'string' ? req.query.driveFileId.trim() : '';
  const jobId = typeof req.query.jobId === 'string' ? req.query.jobId.trim() : '';
  const formatParam: 'video' | 'audio' = req.query.format === 'audio' ? 'audio' : 'video';
  const qualityParam =
    typeof req.query.quality === 'string' ? req.query.quality.trim() : ctx.session.defaultQuality || '720';
  const compressParam: CompressMode =
    req.query.compress === 'zip'
      ? 'zip'
      : req.query.compress === 'media'
      ? 'media'
      : 'none';
  const pathNameParam =
    typeof req.params.pathFileName === 'string' ? req.params.pathFileName.trim() : '';
  const customName =
    (typeof req.query.name === 'string' ? req.query.name.trim() : '') || pathNameParam;

  const abortController = new AbortController();
  req.on('close', () => {
    if (!res.writableEnded) {
      abortController.abort();
    }
  });
  const { signal } = abortController;
  const tempFilesToClean: string[] = [];

  try {
    let targetUrl = rawUrl;
    let targetDriveId = driveFileId;
    let fileName = customName;
    let mimeType = formatParam === 'audio' ? 'audio/mpeg' : 'application/octet-stream';
    let jobSpecificToken: string | null = null;

    if (jobId && !targetUrl && !targetDriveId) {
      const job = transferJobs.find((j) => j.id === jobId);
      if (job) {
        if (job.driveFileId) targetDriveId = job.driveFileId;
        else if (job.directUrl) targetUrl = job.directUrl;
        if (!fileName) fileName = job.fileName;
        if (job.mimeType) mimeType = job.mimeType;
        const jobSess = resolveJobDriveSession(job);
        jobSpecificToken = jobSess.accessToken;
      }
    }

    let upstreamRes: Response | null = null;

    if (targetDriveId) {
      const token = jobSpecificToken || ctx.session.accessToken || driveSession.accessToken;
      if (!token) {
        res.status(401).json({ error: 'يرجى ربط أو تنشيط جلسة حسابك Google Drive من لوحة التحكم أولاً لتحميل هذا الملف.' });
        return;
      }
      const metaRes = await fetch(
        `https://www.googleapis.com/drive/v3/files/${targetDriveId}?fields=id,name,mimeType,size`,
        {
          headers: { Authorization: `Bearer ${token}` },
          signal,
        }
      );
      if (!metaRes.ok) {
        res.status(metaRes.status).json({ error: 'تعذر قراءة بيانات الملف من Google Drive.' });
        return;
      }
      const meta = await metaRes.json();
      if (!fileName) fileName = meta.name || `drive_${targetDriveId}`;
      mimeType = meta.mimeType || mimeType;

      let mediaUrl = `https://www.googleapis.com/drive/v3/files/${targetDriveId}?alt=media`;
      if (mimeType.startsWith('application/vnd.google-apps.')) {
        mediaUrl = `https://www.googleapis.com/drive/v3/files/${targetDriveId}/export?mimeType=application/pdf`;
        if (!fileName.toLowerCase().endsWith('.pdf')) fileName += '.pdf';
        mimeType = 'application/pdf';
      }

      upstreamRes = await fetch(mediaUrl, {
        headers: { Authorization: `Bearer ${token}` },
        signal,
      });
    } else if (targetUrl) {
      const resolved = await resolveTelegramPostLinkIfApplicable(targetUrl, formatParam, qualityParam);
      if (!fileName) {
        fileName = resolved.detectedFileName || extractFilenameFromUrl(targetUrl, formatParam);
      } else if (resolved.detectedFileName && !fileName.includes('.')) {
        const extMatch = resolved.detectedFileName.match(/(\.[^.]+)$/);
        if (extMatch) fileName += extMatch[1];
      }
      if (resolved.detectedMimeType) {
        mimeType = resolved.detectedMimeType;
      }

      upstreamRes = await fetch(resolved.resolvedUrl, {
        signal,
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
          ...(resolved.customHeaders || {}),
        },
      });
    } else {
      res.status(400).json({ error: 'يرجى تمرير رابط صالح (url) أو معرف ملف (driveFileId).' });
      return;
    }

    if (!upstreamRes || !upstreamRes.ok || !upstreamRes.body) {
      res.status(502).json({ error: `تعذر جلب الملف من المصدر (${upstreamRes?.status || 'خطأ'}).` });
      return;
    }

    const upstreamContentType = upstreamRes.headers.get('content-type');
    if (
      upstreamContentType &&
      upstreamContentType.toLowerCase().includes('text/html') &&
      !fileName.toLowerCase().endsWith('.html')
    ) {
      res.status(502).json({ error: 'المصدر أعاد صفحة HTML بدلاً من ملف الفيديو أو الصوت.' });
      return;
    }
    if (upstreamContentType && mimeType === 'application/octet-stream') {
      mimeType = upstreamContentType.split(';')[0].trim();
    }

    if (!fileName) {
      fileName = `download_${Date.now()}.${formatParam === 'audio' ? 'mp3' : 'mp4'}`;
    }

    // If compression is requested before direct download
    if (compressParam !== 'none') {
      const safeName = fileName.replace(/[^a-zA-Z0-9._\u0600-\u06FF-]/g, '_');
      const rawTemp = path.join('/tmp', `dl_raw_${Date.now()}_${safeName}`);
      tempFilesToClean.push(rawTemp);

      const ws = fs.createWriteStream(rawTemp);
      for await (const chunk of readableStreamToAsyncIterable(upstreamRes.body)) {
        if (signal.aborted) {
          ws.destroy();
          return;
        }
        if (chunk && chunk.byteLength > 0) {
          const ok = ws.write(Buffer.from(chunk));
          if (!ok) await new Promise<void>((r) => ws.once('drain', r));
        }
      }
      await new Promise<void>((resolve, reject) => ws.end((e?: Error | null) => (e ? reject(e) : resolve())));

      const comp = await compressLocalFile(rawTemp, fileName, mimeType, compressParam, signal);
      if (comp.finalPath !== rawTemp) {
        tempFilesToClean.push(comp.finalPath);
      }

      const stat = fs.statSync(comp.finalPath);
      const asciiFallback = comp.finalFileName.replace(/[^\x20-\x7E]/g, '_') || 'download';
      res.setHeader('Content-Type', comp.finalMimeType || 'application/octet-stream');
      res.setHeader('Content-Length', String(stat.size));
      res.setHeader(
        'Content-Disposition',
        `attachment; filename="${asciiFallback}"; filename*=UTF-8''${encodeURIComponent(comp.finalFileName)}`
      );

      const rs = fs.createReadStream(comp.finalPath);
      await new Promise<void>((resolve, reject) => {
        rs.pipe(res);
        rs.on('end', resolve);
        rs.on('error', reject);
      });
      return;
    }

    // Direct zero-copy stream to user's browser
    const asciiFallback = fileName.replace(/[^\x20-\x7E]/g, '_') || 'download';
    res.setHeader('Content-Type', mimeType || 'application/octet-stream');
    const contentLen = upstreamRes.headers.get('content-length');
    const contentEnc = upstreamRes.headers.get('content-encoding');
    if (contentLen && !contentEnc) {
      res.setHeader('Content-Length', contentLen);
    }
    res.setHeader(
      'Content-Disposition',
      `attachment; filename="${asciiFallback}"; filename*=UTF-8''${encodeURIComponent(fileName)}`
    );

    for await (const chunk of readableStreamToAsyncIterable(upstreamRes.body)) {
      if (signal.aborted || res.writableEnded) break;
      if (chunk && chunk.byteLength > 0) {
        const canWrite = res.write(Buffer.from(chunk));
        if (!canWrite) {
          await new Promise<void>((r) => res.once('drain', r));
        }
      }
    }
    res.end();
  } catch (err: any) {
    if (!res.headersSent) {
      res.status(500).json({ error: err?.message || 'حدث خطأ أثناء التحميل المباشر للملف.' });
    } else if (!res.writableEnded) {
      res.end();
    }
  } finally {
    for (const f of tempFilesToClean) {
      if (f && fs.existsSync(f)) {
        try {
          fs.unlinkSync(f);
        } catch {
          // Ignore
        }
      }
    }
  }
});

// Pull a file from Google Drive and send it directly to the user's Telegram chat
app.post('/api/telegram/send-drive-file', async (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const authHeader = req.headers.authorization;
  if (authHeader && authHeader.startsWith('Bearer ')) {
    ctx.profile.accessToken = authHeader.replace('Bearer ', '').trim();
  }

  const { driveFileId, fileName, mimeType, size, targetChatId, compressMode } = req.body || {};
  if (!driveFileId) {
    res.status(400).json({ error: 'معرف ملف Google Drive مطلوب.' });
    return;
  }

  const resolvedChatId =
    Number(targetChatId) ||
    ctx.chatId ||
    ctx.profile.chatId ||
    adminConfig.ownerChatId ||
    Object.values(adminConfig.knownUsers)[0]?.chatId ||
    transferJobs.find((j) => j.chatId)?.chatId;

  if (!resolvedChatId) {
    res.status(400).json({
      error:
        'يرجى ربط حسابك في تليجرام أولاً عبر زر "ربط حسابي في تليجرام" في أعلى الصفحة أو إرسال /start للبوت.',
    });
    return;
  }

  const resolvedCompress: CompressMode =
    compressMode === 'zip' || compressMode === 'media' || compressMode === 'none'
      ? compressMode
      : ctx.session.defaultCompressMode || 'none';

  const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
  const statusMsgId = await sendTelegramMessage(
    resolvedChatId,
    `📥 <b>تم طلب إرسال ملف من حسابك Google Drive إلى تليجرام...</b>\n📄 <code>${fileName || driveFileId}</code>`,
    undefined,
    {
      inline_keyboard: [[{ text: '⛔ إلغاء السحب', callback_data: `cancel_${jobId}` }]],
    }
  );

  const job: TransferJob = {
    id: jobId,
    source: 'drive_to_telegram',
    direction: 'to_telegram',
    compressMode: resolvedCompress,
    fileName: fileName || `drive_${driveFileId}`,
    mimeType: mimeType || 'application/octet-stream',
    totalBytes: Number(size) || 0,
    bytesTransferred: 0,
    speedBps: 0,
    status: 'queued',
    senderName: ctx.session.userName || 'سحب من Drive إلى تليجرام',
    accountEmail: ctx.session.userEmail || 'default',
    chatId: resolvedChatId,
    statusMessageId: statusMsgId,
    driveFileId,
    createdAt: new Date().toISOString(),
  };

  transferJobs.unshift(job);
  saveStateToDisk();
  if (IS_VERCEL) {
    await executePullToTelegramJob(job);
  } else {
    executePullToTelegramJob(job);
  }

  res.json({ ok: true, job });
});

app.post('/api/transfers/url', async (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const authHeader = req.headers.authorization;
  if (authHeader && authHeader.startsWith('Bearer ')) {
    ctx.profile.accessToken = authHeader.replace('Bearer ', '').trim();
  }

  const { url, customFileName, destination, targetChatId, mediaFormat, quality, compressMode } = req.body || {};
  const cleanUrl = extractCleanHttpUrl(typeof url === 'string' ? url : '');
  if (!cleanUrl || !/^https?:\/\//i.test(cleanUrl)) {
    res.status(400).json({ error: 'يرجى إدخال رابط مباشر صالح يبدأ بـ http:// أو https://' });
    return;
  }

  const resolvedFormat: 'video' | 'audio' = mediaFormat === 'audio' ? 'audio' : 'video';
  const resolvedQuality =
    typeof quality === 'string' && quality.trim() ? quality.trim() : ctx.session.defaultQuality || '720';
  const resolvedCompress: CompressMode =
    compressMode === 'zip' || compressMode === 'media' || compressMode === 'none'
      ? compressMode
      : ctx.session.defaultCompressMode || 'none';

  try {
    // Validate and resolve URL upfront to provide immediate feedback for unsupported link types (e.g. Telegram post links)
    const resolvedMedia = await resolveTelegramPostLinkIfApplicable(cleanUrl, resolvedFormat, resolvedQuality);
    const fileName =
      (customFileName || '').trim() ||
      resolvedMedia.detectedFileName ||
      extractFilenameFromUrl(cleanUrl, resolvedFormat);

    const isToTelegram = destination === 'telegram';

    if (isToTelegram) {
      const resolvedChatId =
        Number(targetChatId) ||
        ctx.chatId ||
        ctx.profile.chatId ||
        adminConfig.ownerChatId ||
        Object.values(adminConfig.knownUsers)[0]?.chatId ||
        transferJobs.find((j) => j.chatId)?.chatId;

      if (!resolvedChatId) {
        res.status(400).json({
          error:
            'يرجى ربط حسابك في تليجرام أولاً عبر زر "ربط حسابي في تليجرام" لإرسال الرابط إلى محادثتك الخاصة.',
        });
        return;
      }

      const jobId = `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
      let statusMsgId: number | undefined;
      try {
        statusMsgId = await sendTelegramMessage(
          resolvedChatId,
          `📥 <b>جاري سحب الرابط (${resolvedFormat === 'audio' ? `${resolvedQuality}kbps MP3` : `${resolvedQuality}p`})${
            resolvedCompress !== 'none' ? ` مع الضغط (${formatCompressModeAr(resolvedCompress)})` : ''
          } وإرساله إلى تليجرام...</b>\n📄 <code>${fileName}</code>`,
          undefined,
          {
            inline_keyboard: [[{ text: '⛔ إلغاء السحب', callback_data: `cancel_${jobId}` }]],
          }
        );
      } catch (tgErr: any) {
        console.warn('Could not send initial Telegram status message:', tgErr?.message);
      }

      const job: TransferJob = {
        id: jobId,
        source: 'url_to_telegram',
        direction: 'to_telegram',
        protocol: 'http',
        mediaFormat: resolvedFormat,
        quality: resolvedQuality,
        compressMode: resolvedCompress,
        fileName,
        mimeType: resolvedFormat === 'audio' ? 'audio/mpeg' : 'application/octet-stream',
        totalBytes: 0,
        bytesTransferred: 0,
        speedBps: 0,
        status: 'queued',
        senderName: ctx.session.userName || 'لوحة التحكم (رابط إلى تليجرام)',
        accountEmail: ctx.session.userEmail || 'default',
        chatId: resolvedChatId,
        statusMessageId: statusMsgId,
        directUrl: resolvedMedia.resolvedUrl || cleanUrl,
        createdAt: new Date().toISOString(),
      };

      transferJobs.unshift(job);
      saveStateToDisk();
      executePullToTelegramJob(job).catch((err) => {
        console.error('executePullToTelegramJob error:', err?.message);
      });
      res.json({ ok: true, job });
      return;
    }

    const canUpload = Boolean(ctx.session.accessToken && ctx.session.accountEnabled);
    const job: TransferJob = {
      id: `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
      source: 'url',
      direction: 'to_drive',
      protocol: 'http',
      mediaFormat: resolvedFormat,
      quality: resolvedQuality,
      compressMode: resolvedCompress,
      fileName,
      mimeType: resolvedFormat === 'audio' ? 'audio/mpeg' : 'application/octet-stream',
      totalBytes: 0,
      bytesTransferred: 0,
      speedBps: 0,
      status: canUpload ? 'queued' : 'waiting_auth',
      senderName: ctx.session.userName || 'لوحة التحكم (رابط مباشر)',
      accountEmail: ctx.session.userEmail || 'default',
      chatId: ctx.chatId || undefined,
      directUrl: resolvedMedia.resolvedUrl || cleanUrl,
      folderName: ctx.session.activeFolderName,
      createdAt: new Date().toISOString(),
    };

    transferJobs.unshift(job);
    saveStateToDisk();
    if (canUpload) {
      executeTransferJob(job).catch((err) => {
        console.error('executeTransferJob error:', err?.message);
      });
    }

    res.json({ ok: true, job });
  } catch (err: any) {
    res.status(400).json({
      error: err?.message || 'تعذر معالجة الرابط المدخل. يرجى التأكد من صلاحية الرابط.',
    });
  }
});

app.post('/api/transfers/register-web', (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const { fileName, mimeType, totalBytes, driveFileId, webViewLink, folderName } = req.body || {};
  const job: TransferJob = {
    id: `job_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
    source: 'web',
    direction: 'to_drive',
    fileName: fileName || 'file',
    mimeType: mimeType || 'application/octet-stream',
    totalBytes: Number(totalBytes) || 0,
    bytesTransferred: Number(totalBytes) || 0,
    speedBps: 0,
    status: 'completed',
    senderName: ctx.session.userName || 'رفع مباشر من المتصفح',
    accountEmail: ctx.session.userEmail || 'default',
    chatId: ctx.chatId || undefined,
    driveFileId,
    webViewLink: webViewLink || (driveFileId ? `https://drive.google.com/file/d/${driveFileId}/view` : undefined),
    folderName: folderName || ctx.session.activeFolderName,
    createdAt: new Date().toISOString(),
    completedAt: new Date().toISOString(),
  };
  transferJobs.unshift(job);
  saveStateToDisk();
  res.json({ ok: true, job });
});

app.post('/api/transfers/:id/retry', async (req, res) => {
  const job = transferJobs.find((j) => j.id === req.params.id);
  if (!job) {
    res.status(404).json({ error: 'لم يتم العثور على العملية.' });
    return;
  }
  job.bytesTransferred = 0;
  job.speedBps = 0;
  job.errorMessage = undefined;
  const sess = resolveJobDriveSession(job);
  if (job.direction === 'to_telegram' || job.source === 'drive_to_telegram' || job.source === 'url_to_telegram') {
    job.status = 'queued';
    saveStateToDisk();
    executePullToTelegramJob(job);
  } else {
    job.status = sess.accessToken && sess.accountEnabled ? 'queued' : 'waiting_auth';
    saveStateToDisk();
    if (sess.accessToken && sess.accountEnabled) {
      executeTransferJob(job);
    }
  }
  res.json({ ok: true, job });
});

// Cancel a single ongoing or queued transfer
app.post('/api/transfers/:id/cancel', (req, res) => {
  const job = cancelTransferJobById(req.params.id);
  if (!job) {
    res.status(404).json({ error: 'لم يتم العثور على العملية.' });
    return;
  }
  res.json({ ok: true, job });
});

// Cancel all active/queued transfers (scoped to user if provided)
app.post('/api/transfers/cancel-all', (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const scopeAll = req.body?.scope === 'all';
  const active = scopeAll ? getActiveJobsList() : getActiveJobsList(ctx.chatId || undefined);
  for (const j of active) {
    cancelTransferJobById(j.id);
  }
  res.json({ ok: true, cancelledCount: active.length });
});

// Clear all failed and cancelled jobs from transfer history
app.delete('/api/transfers/failed/clear', (req, res) => {
  const ctx = resolveRequestUserContext(req);
  const removedCount = clearAllFailedAndCancelledJobs(ctx.chatId || undefined, ctx.userEmail);
  res.json({ ok: true, removedCount });
});

// Delete a single job from transfer history
app.delete('/api/transfers/:id', (req, res) => {
  const jobId = req.params.id;
  const idx = transferJobs.findIndex((j) => j.id === jobId);
  if (idx === -1) {
    res.status(404).json({ error: 'لم يتم العثور على العملية.' });
    return;
  }
  const controller = jobAbortControllers.get(jobId);
  if (controller) {
    controller.abort();
    jobAbortControllers.delete(jobId);
  }
  transferJobs.splice(idx, 1);
  saveStateToDisk();
  res.json({ ok: true });
});

async function bootstrap() {
  if (process.env.NODE_ENV !== 'production') {
    const { createServer: createViteServer } = await import('vite');
    const vite = await createViteServer({
      server: { middlewareMode: true },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    const distPath = path.join(process.cwd(), 'dist');
    app.use(express.static(distPath));
    app.get('*', (_req, res) => {
      res.sendFile(path.join(distPath, 'index.html'));
    });
  }

  app.listen(PORT, '0.0.0.0', () => {
    console.log(`Server listening on http://0.0.0.0:${PORT}`);
  });
}

if (!IS_VERCEL) {
  bootstrap();
}

export default app;
