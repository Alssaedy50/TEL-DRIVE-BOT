import React, { useState, useEffect, useRef, useCallback } from 'react';
import {
  Send,
  HardDrive,
  FolderPlus,
  RefreshCw,
  CheckCircle2,
  AlertTriangle,
  ExternalLink,
  FileText,
  UploadCloud,
  Trash2,
  Copy,
  Check,
  Search,
  LogOut,
  Bot,
  Activity,
  FolderCheck,
  Loader2,
  X,
  Link2,
  Ban,
  Settings,
  ShieldAlert,
  Power,
  Globe,
  Download,
  Smartphone,
  Sliders,
  User,
  Menu,
  ChevronLeft,
  ArrowRight,
  Pause,
  Play,
  FileArchive,
  Film,
  Music,
  ClipboardPaste,
  WifiOff,
  Share2,
  PlusSquare,
} from 'lucide-react';
import {
  listFolders,
  createFolder,
  listFiles,
  deleteFile,
  startResumableUpload,
  uploadChunk,
  type DriveFile,
  type DriveFolder,
} from './services/googleDrive';
import firebaseConfig from '../firebase-applet-config.json';
import {
  googleSignIn,
  initAuth,
  logout as firebaseLogout,
  saveStoredToken,
  clearStoredToken,
} from './firebase';
import { usePWAInstall } from './usePWAInstall';

declare global {
  interface Window {
    google: any;
  }
}

const SCOPES = 'https://www.googleapis.com/auth/drive.file';
const STORAGE_EMAIL_KEY = 'tg_drive_personal_email';
const STORAGE_NAME_KEY = 'tg_drive_personal_name';
const STORAGE_CHAT_ID_KEY = 'tg_drive_personal_chat_id';
const STORAGE_CUSTOM_CLIENT_ID_KEY = 'tg_drive_custom_google_client_id';
const STORAGE_VERCEL_URL_KEY = 'tg_drive_target_vercel_url';

type CompressMode = 'none' | 'zip' | 'media';
type ModalType = 'menu' | 'drive_files' | 'large_upload' | 'settings' | 'admin' | 'url_options' | 'pwa_install' | null;

interface TransferJob {
  id: string;
  source?: 'telegram' | 'url' | 'web' | 'drive_to_telegram' | 'url_to_telegram';
  direction?: 'to_drive' | 'to_telegram' | 'to_device';
  protocol?: 'bot_api' | 'mtproto' | 'http';
  mediaFormat?: 'video' | 'audio';
  quality?: string;
  compressMode?: CompressMode;
  fileName: string;
  mimeType: string;
  totalBytes: number;
  bytesTransferred: number;
  speedBps?: number;
  status: 'queued' | 'downloading' | 'uploading' | 'completed' | 'failed' | 'waiting_auth' | 'cancelled';
  isDuplicateSkipped?: boolean;
  errorMessage?: string;
  senderName: string;
  senderUsername?: string;
  accountEmail?: string;
  chatId?: number;
  driveFileId?: string;
  webViewLink?: string;
  directUrl?: string;
  folderName?: string;
  createdAt: string;
  completedAt?: string;
}

interface AvailableMediaFormat {
  id: string;
  format: 'video' | 'audio';
  quality: string;
  label: string;
  badge: string;
  ext: string;
  sizeBytes: number;
  mediaCompressedBytes?: number;
  zipCompressedBytes?: number;
  savedPercent: number;
  isSelected: boolean;
  fileName: string;
  zipFileName: string;
  sourceStreamUrl?: string;
  mediaStreamUrl?: string;
  requiresWorkerForOriginal?: boolean;
  requiresWorkerForMedia?: boolean;
  downloadUrl: string;
  mediaDownloadUrl?: string;
  zipDownloadUrl: string;
}

interface ResolvedMediaInfo {
  jobId: string;
  title: string;
  fileName: string;
  mimeType: string;
  sizeBytes: number;
  originalSizeBytes: number;
  compressedSizeBytes: number;
  savedBytes: number;
  savedPercent: number;
  compressMode: CompressMode;
  mediaFormat: 'video' | 'audio';
  quality: string;
  effectiveQuality: string;
  platformName: string;
  isVideoPlatform: boolean;
  zipEligible?: boolean;
  zipSavedPercent?: number;
  durationSec: number;
  directStreamUrl: string;
  proxyDownloadUrl: string;
  preferDirectCdn: boolean;
  availableFormats: AvailableMediaFormat[];
}

function evaluateFileLosslessZipInfo(
  fileName: string,
  mimeType?: string
): { zipEligible: boolean; zipSavedPercent: number } {
  const lowerName = (fileName || '').toLowerCase();
  const lowerMime = (mimeType || '').toLowerCase();
  const isUncompressedMedia = /\.(wav|aiff|pcm|bmp|tiff|tga|raw|svg)$/i.test(lowerName);
  if (
    !isUncompressedMedia &&
    (lowerMime.startsWith('video/') ||
      lowerMime.startsWith('audio/') ||
      /\.(mp4|mkv|webm|mov|avi|flv|m4v|3gp|mp3|m4a|aac|ogg|opus|flac|wma|zip|rar|7z|gz|tgz|bz2|xz|zst|apk|ipa|dmg|deb|rpm|jpg|jpeg|png|webp|gif|heic|avif)$/i.test(
        lowerName
      ))
  ) {
    return { zipEligible: false, zipSavedPercent: 2 };
  }
  if (
    /\.(txt|csv|tsv|json|xml|yaml|yml|sql|log|md|html|htm|css|js|ts|jsx|tsx|py|java|c|cpp|h|cs|php|rb|go|rs|srt|vtt|ass|sub|svg)$/i.test(
      lowerName
    ) ||
    lowerMime.startsWith('text/') ||
    lowerMime.includes('json') ||
    lowerMime.includes('xml') ||
    lowerMime.includes('svg')
  ) {
    return { zipEligible: true, zipSavedPercent: 62 };
  }
  if (/\.(bmp|wav|aiff|pcm|tar|iso|psd|ai|eps|ttf|otf|exe|dll|so|bin|db|sqlite|sqlite3|mdb|dbf|vcf|ics)$/i.test(lowerName)) {
    return { zipEligible: true, zipSavedPercent: 38 };
  }
  if (
    /\.(pdf|doc|docx|xls|xlsx|ppt|pptx|rtf|odt|ods|odp|epub|mobi)$/i.test(lowerName) ||
    lowerMime.includes('pdf') ||
    lowerMime.includes('msword') ||
    lowerMime.includes('officedocument') ||
    lowerMime.includes('spreadsheet') ||
    lowerMime.includes('presentation')
  ) {
    return { zipEligible: true, zipSavedPercent: 22 };
  }
  return { zipEligible: false, zipSavedPercent: 4 };
}

interface InAppDownloadState {
  id: string;
  fileName: string;
  formatLabel: string;
  compressMode: CompressMode;
  originalBytes: number;
  totalBytes: number;
  bytesLoaded: number;
  percent: number;
  speedBps: number;
  status: 'worker_processing' | 'downloading' | 'paused' | 'completed' | 'cancelled' | 'failed';
  workerJobId?: string;
  workerStageLabel?: string;
  errorMessage?: string;
  blobUrl?: string;
}

interface KnownTelegramUser {
  chatId: number;
  name: string;
  username?: string;
  lastSeenAt: string;
  transfersCount: number;
  blocked: boolean;
  linkedEmail?: string | null;
  driveConnected?: boolean;
}

interface ServerStatus {
  deployment?: {
    isVercel: boolean;
    mode: 'webhook' | 'polling';
    webhookUrl: string | null;
    appUrl: string;
  };
  bot: {
    configured: boolean;
    connected: boolean;
    info: {
      id: number;
      first_name: string;
      username?: string;
    } | null;
    error: string | null;
    apiRoot?: string;
    isCustomApiRoot?: boolean;
    mtproto?: {
      configured: boolean;
      connected: boolean;
      error: string | null;
      maxFileSizeLabel: string;
    };
  };
  drive: {
    connected: boolean;
    activeAccessToken?: string | null;
    accountEnabled: boolean;
    userEmail: string | null;
    userName: string | null;
    activeFolderId: string | null;
    activeFolderName: string;
    autoCategorizeByType?: boolean;
    skipDuplicates?: boolean;
    urlHandlingMode?: 'ask' | 'to_drive' | 'to_telegram';
    defaultQuality?: string;
    defaultCompressMode?: CompressMode;
    lastSyncedAt: string | null;
    linkCode?: string;
    linkedChatId?: number | null;
    linkedTelegramName?: string | null;
    linkedTelegramUsername?: string | null;
  };
  admin?: {
    ownerChatId: number | null;
    ownerName: string | null;
    ownerUsername: string | null;
    accessMode: 'public' | 'owner_only';
    botPaused: boolean;
    knownUsers: KnownTelegramUser[];
    connectedProfilesCount?: number;
    globalStats?: {
      totalJobs: number;
      completedJobs: number;
      activeJobs: number;
      waitingAuthJobs: number;
      failedJobs: number;
      totalBytesTransferred: number;
    };
    globalActiveJobs?: TransferJob[];
  };
  stats: {
    totalJobs: number;
    completedJobs: number;
    activeJobs: number;
    waitingAuthJobs: number;
    failedJobs: number;
    totalBytesTransferred: number;
  };
  jobs: TransferJob[];
}

async function parseJsonResponse<T = any>(res: Response, fallbackErrorMsg = 'تعذر إتمام العملية'): Promise<T> {
  const text = await res.text();
  let json: any = null;
  try {
    json = JSON.parse(text);
  } catch {
    if (res.status === 500 || text.includes('A server error has occurred')) {
      throw new Error('حدث خطأ في خادم Vercel (500). يرجى التأكد من نشر أحدث التعديلات وإعادة المحاولة.');
    }
    if (res.status === 504) {
      throw new Error('انتهت مهلة استجابة الخادم (504 Gateway Timeout). حاول مرة أخرى.');
    }
    if (res.status === 404) {
      throw new Error('مسار الخدمة المطلوب غير متاح على الخادم (404).');
    }
    throw new Error(`تعذر قراءة استجابة الخادم (${res.status}): ${text.slice(0, 80)}`);
  }

  if (!res.ok) {
    throw new Error(json?.error || fallbackErrorMsg);
  }
  return json as T;
}

export default function App() {
  // Personal Identity State (Multi-User Personal Account Support)
  const [personalEmail, setPersonalEmail] = useState<string>(() => {
    return localStorage.getItem(STORAGE_EMAIL_KEY) || '';
  });
  const [personalName, setPersonalName] = useState<string>(() => {
    return localStorage.getItem(STORAGE_NAME_KEY) || '';
  });
  const [personalChatId, setPersonalChatId] = useState<string>(() => {
    const params = new URLSearchParams(window.location.search);
    const fromQuery = params.get('chatId');
    if (fromQuery && /^-?\d+$/.test(fromQuery.trim())) {
      localStorage.setItem(STORAGE_CHAT_ID_KEY, fromQuery.trim());
      return fromQuery.trim();
    }
    return localStorage.getItem(STORAGE_CHAT_ID_KEY) || '';
  });

  // Custom Google Client ID & Vercel Session Bridge support
  const [customClientId, setCustomClientId] = useState<string>(() => {
    return localStorage.getItem(STORAGE_CUSTOM_CLIENT_ID_KEY) || '';
  });
  const [unauthorizedDomainHost, setUnauthorizedDomainHost] = useState<string | null>(null);
  const [copiedDomain, setCopiedDomain] = useState(false);
  const [copiedOrigin, setCopiedOrigin] = useState(false);
  const [sessionCodeInput, setSessionCodeInput] = useState('');
  const [applyingSessionCode, setApplyingSessionCode] = useState(false);
  const [targetVercelUrl, setTargetVercelUrl] = useState<string>(() => {
    return localStorage.getItem(STORAGE_VERCEL_URL_KEY) || '';
  });
  const [pushingToVercel, setPushingToVercel] = useState(false);
  const [copiedSessionCode, setCopiedSessionCode] = useState(false);
  const [magicLoginUrlResult, setMagicLoginUrlResult] = useState<string | null>(null);

  // Google OAuth state
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [userProfile, setUserProfile] = useState<{ name: string; email: string; picture?: string } | null>(null);
  const tokenClientRef = useRef<any>(null);

  // Server & Bot state
  const [serverStatus, setServerStatus] = useState<ServerStatus | null>(null);
  const [reconnectingBot, setReconnectingBot] = useState(false);
  const [autoCategorize, setAutoCategorize] = useState(true);
  const [skipDuplicates, setSkipDuplicates] = useState(true);

  // Popup Modal State ('menu' opens the popup launcher; each option opens its own popup page)
  const [activeModal, setActiveModal] = useState<ModalType>(null);
  const [savingSettings, setSavingSettings] = useState(false);
  const [sendingDriveFileId, setSendingDriveFileId] = useState<string | null>(null);

  // Google Drive Folders & Files state
  const [folders, setFolders] = useState<DriveFolder[]>([]);
  const [selectedFolderId, setSelectedFolderId] = useState<string>('');
  const [selectedFolderName, setSelectedFolderName] = useState<string>('Telegram Bot Uploads');
  const [newFolderInput, setNewFolderInput] = useState('');
  const [creatingFolder, setCreatingFolder] = useState(false);

  const [driveFiles, setDriveFiles] = useState<DriveFile[]>([]);
  const [filesLoading, setFilesLoading] = useState(false);
  const [searchQuery, setSearchQuery] = useState('');
  const [copiedId, setCopiedId] = useState<string | null>(null);
  const [confirmDeleteId, setConfirmDeleteId] = useState<string | null>(null);
  const [copiedLinkCode, setCopiedLinkCode] = useState(false);

  // Direct Web Resumable Upload state (for local multi-GB files)
  const [uploadingLocal, setUploadingLocal] = useState(false);
  const [localUploadProgress, setLocalUploadProgress] = useState(0);
  const [localUploadFileName, setLocalUploadFileName] = useState('');

  // PWA Install & Connectivity state
  const { isInstallable, isInstalled, isIOS, isOnline, install: triggerPwaInstall } = usePWAInstall();

  // Multi-platform URL Uploader state
  const [externalUrlInput, setExternalUrlInput] = useState('');
  const [externalCustomName, setExternalCustomName] = useState('');
  const [externalDestination, setExternalDestination] = useState<'drive' | 'telegram' | 'device'>('device');
  const [externalMediaFormat, setExternalMediaFormat] = useState<'video' | 'audio'>('video');
  const [externalQuality, setExternalQuality] = useState<string>('720');
  const [externalCompressMode, setExternalCompressMode] = useState<CompressMode>('none');
  const [submittingUrl, setSubmittingUrl] = useState(false);
  const [inspectingUrl, setInspectingUrl] = useState(false);
  const lastInspectedUrlRef = useRef<string>('');
  const [clearingFailed, setClearingFailed] = useState(false);
  const [downloadingItemId, setDownloadingItemId] = useState<string | null>(null);
  const [lastDirectDownload, setLastDirectDownload] = useState<{ url: string; fileName: string } | null>(null);
  const [resolvedMediaInfo, setResolvedMediaInfo] = useState<ResolvedMediaInfo | null>(null);
  const [inAppDownload, setInAppDownload] = useState<InAppDownloadState | null>(null);

  // Refs for in-app streaming download control (Pause / Resume / Cancel)
  const downloadAbortRef = useRef<AbortController | null>(null);
  const downloadPausedRef = useRef<boolean>(false);
  const downloadResumeResolverRef = useRef<(() => void) | null>(null);

  // Alerts
  const [bannerError, setBannerError] = useState<string | null>(null);
  const [bannerSuccess, setBannerSuccess] = useState<string | null>(null);

  const hasCustomOrEnvClientId = Boolean(
    customClientId.trim() || (import.meta as any).env?.VITE_GOOGLE_CLIENT_ID
  );
  const clientId =
    customClientId.trim() ||
    (import.meta as any).env?.VITE_GOOGLE_CLIENT_ID ||
    (firebaseConfig as any)?.oAuthClientId ||
    '';

  // Close popup modal on Escape key
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.key === 'Escape') setActiveModal(null);
    };
    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, []);

  const buildIdentityQuery = useCallback(
    (extra?: Record<string, string>) => {
      const q = new URLSearchParams();
      if (personalEmail) q.set('userEmail', personalEmail);
      if (personalChatId) q.set('chatId', personalChatId);
      if (extra) {
        Object.entries(extra).forEach(([k, v]) => {
          if (v !== undefined && v !== null && v !== '') q.set(k, v);
        });
      }
      const str = q.toString();
      return str ? `?${str}` : '';
    },
    [personalEmail, personalChatId]
  );

  // Poll backend status
  const fetchStatus = useCallback(async () => {
    try {
      const res = await fetch(`/api/status${buildIdentityQuery()}`);
      if (!res.ok) return;
      const data: ServerStatus = await res.json();
      setServerStatus(data);
      if (typeof data.drive.autoCategorizeByType === 'boolean') {
        setAutoCategorize(data.drive.autoCategorizeByType);
      }
      if (typeof data.drive.skipDuplicates === 'boolean') {
        setSkipDuplicates(data.drive.skipDuplicates);
      }
      if (data.drive.activeFolderId && !selectedFolderId) {
        setSelectedFolderId(data.drive.activeFolderId);
        setSelectedFolderName(data.drive.activeFolderName);
      }
      if (data.drive.linkedChatId && !personalChatId) {
        const cid = String(data.drive.linkedChatId);
        setPersonalChatId(cid);
        localStorage.setItem(STORAGE_CHAT_ID_KEY, cid);
      }
      if (data.drive.connected && data.drive.activeAccessToken && !accessToken) {
        setAccessToken(data.drive.activeAccessToken);
        saveStoredToken(data.drive.activeAccessToken);
        if (data.drive.userEmail && !personalEmail) {
          setPersonalEmail(data.drive.userEmail);
          localStorage.setItem(STORAGE_EMAIL_KEY, data.drive.userEmail);
        }
        if (data.drive.userName && !personalName) {
          setPersonalName(data.drive.userName);
          localStorage.setItem(STORAGE_NAME_KEY, data.drive.userName);
        }
      }
    } catch {
      // Ignore transient poll errors
    }
  }, [buildIdentityQuery, selectedFolderId, personalChatId, accessToken, personalEmail, personalName]);

  useEffect(() => {
    fetchStatus();
    const interval = setInterval(fetchStatus, 1800);
    return () => clearInterval(interval);
  }, [fetchStatus]);

  // Initialize Firebase Auth & Google Identity Services fallback
  useEffect(() => {
    const unsubscribe = initAuth(
      (user, token) => {
        setAccessToken(token);
        setUnauthorizedDomainHost(null);
        onGoogleAuthenticated(token, {
          name: user.displayName || undefined,
          email: user.email || undefined,
          picture: user.photoURL || undefined,
        });
      },
      () => {}
    );

    if (clientId) {
      const initGis = () => {
        if (!window.google?.accounts?.oauth2) return;
        tokenClientRef.current = window.google.accounts.oauth2.initTokenClient({
          client_id: clientId,
          scope: `${SCOPES} https://www.googleapis.com/auth/userinfo.profile https://www.googleapis.com/auth/userinfo.email`,
          callback: async (tokenResponse: any) => {
            if (tokenResponse.error) {
              setBannerError(`فشل تسجيل الدخول إلى Google: ${tokenResponse.error}`);
              return;
            }
            const token = tokenResponse.access_token;
            saveStoredToken(token);
            setAccessToken(token);
            setUnauthorizedDomainHost(null);
            setBannerError(null);
            await onGoogleAuthenticated(token);
          },
        });
      };

      if (window.google?.accounts?.oauth2) {
        initGis();
      } else {
        const script = document.createElement('script');
        script.src = 'https://accounts.google.com/gsi/client';
        script.async = true;
        script.defer = true;
        script.onload = initGis;
        document.body.appendChild(script);
      }
    }

    return () => {
      if (typeof unsubscribe === 'function') unsubscribe();
    };
  }, [clientId]);

  const syncTokenWithServer = async (
    token: string,
    email: string,
    name: string,
    folderId?: string,
    folderName?: string,
    categorizeOverride?: boolean,
    dedupOverride?: boolean
  ) => {
    const res = await fetch('/api/drive/sync', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        Authorization: `Bearer ${token}`,
      },
      body: JSON.stringify({
        userEmail: email,
        userName: name,
        chatId: personalChatId || undefined,
        folderId,
        folderName: folderName || selectedFolderName || 'Telegram Bot Uploads',
        autoCategorize: categorizeOverride !== undefined ? categorizeOverride : autoCategorize,
        deduplicate: dedupOverride !== undefined ? dedupOverride : skipDuplicates,
      }),
    });
    const data = await parseJsonResponse(res, 'تعذر مزامنة جلسة حسابك مع الخادم.');
    return data;
  };

  const onGoogleAuthenticated = async (
    token: string,
    knownProfile?: { name?: string; email?: string; picture?: string }
  ) => {
    try {
      let name = knownProfile?.name || 'مستخدم Google Drive';
      let email = knownProfile?.email || '';
      let picture: string | undefined = knownProfile?.picture;

      if (!email) {
        try {
          const userRes = await fetch('https://www.googleapis.com/oauth2/v3/userinfo', {
            headers: { Authorization: `Bearer ${token}` },
          });
          if (userRes.ok) {
            const profile = await userRes.json();
            name = profile.name || name;
            email = profile.email || email;
            picture = profile.picture || picture;
          }
        } catch {
          // Ignore profile fetch error
        }
      }

      setUserProfile({ name, email, picture });
      if (email) {
        setPersonalEmail(email);
        localStorage.setItem(STORAGE_EMAIL_KEY, email);
      }
      if (name) {
        setPersonalName(name);
        localStorage.setItem(STORAGE_NAME_KEY, name);
      }

      const syncData = await syncTokenWithServer(token, email, name);
      setSelectedFolderId(syncData.activeFolderId);
      setSelectedFolderName(syncData.activeFolderName);
      setBannerSuccess(`تم ربط حسابك الشخصي (${email || name}) ومجلد "${syncData.activeFolderName}" بنجاح!`);
      setTimeout(() => setBannerSuccess(null), 5000);

      await refreshDriveFoldersAndFiles(token);
      fetchStatus();
    } catch (err: any) {
      setBannerError(err?.message || 'حدث خطأ أثناء إعداد مجلد Google Drive.');
    }
  };

  const refreshDriveFoldersAndFiles = async (token = accessToken) => {
    if (!token) return;
    setFilesLoading(true);
    try {
      const [fetchedFolders, fetchedFiles] = await Promise.all([listFolders(token), listFiles(token)]);
      setFolders(fetchedFolders);
      setDriveFiles(fetchedFiles);
    } catch (err: any) {
      setBannerError(err?.message || 'تعذر جلب الملفات والمجلدات من Google Drive.');
    } finally {
      setFilesLoading(false);
    }
  };

  const applyPortableSessionCode = async (rawCode: string) => {
    const clean = rawCode.trim();
    if (!clean) return;
    setApplyingSessionCode(true);
    setBannerError(null);
    try {
      let token = clean;
      let email = personalEmail;
      let name = personalName || 'مستخدم Google Drive';
      let chatId = personalChatId;

      if (clean.startsWith('TD1_')) {
        const b64 = clean.slice(4).replace(/-/g, '+').replace(/_/g, '/');
        const binary = atob(b64);
        const bytes = Uint8Array.from(binary, (c) => c.charCodeAt(0));
        const decodedJson = JSON.parse(new TextDecoder().decode(bytes));
        if (!decodedJson?.t) {
          throw new Error('كود الجلسة غير صالح.');
        }
        token = decodedJson.t;
        if (decodedJson.e) email = decodedJson.e;
        if (decodedJson.n) name = decodedJson.n;
        if (decodedJson.c) chatId = String(decodedJson.c);
      }

      if (chatId) {
        setPersonalChatId(chatId);
        localStorage.setItem(STORAGE_CHAT_ID_KEY, chatId);
      }
      saveStoredToken(token);
      setAccessToken(token);
      setUnauthorizedDomainHost(null);
      setSessionCodeInput('');
      await onGoogleAuthenticated(token, { name, email });
    } catch (err: any) {
      setBannerError(err?.message || 'كود الجلسة المدخل غير صالح أو منتهي الصلاحية.');
    } finally {
      setApplyingSessionCode(false);
    }
  };

  // Auto-apply ?magicAuth=TD1_... when opening Vercel via Magic Link
  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const magic = params.get('magicAuth');
    if (magic && magic.trim()) {
      params.delete('magicAuth');
      const nextQuery = params.toString();
      const nextUrl = `${window.location.pathname}${nextQuery ? `?${nextQuery}` : ''}${window.location.hash}`;
      window.history.replaceState({}, '', nextUrl);
      applyPortableSessionCode(magic.trim());
    }
  }, []);

  const handleCopyPortableSessionCode = async () => {
    setBannerError(null);
    try {
      const headers: Record<string, string> = {};
      if (accessToken) headers.Authorization = `Bearer ${accessToken}`;
      const res = await fetch(`/api/drive/export-session${buildIdentityQuery()}`, { headers });
      const data = await parseJsonResponse(res, 'تعذر استخراج كود الجلسة.');
      if (!data.sessionCode) {
        throw new Error(data.error || 'تعذر استخراج كود الجلسة.');
      }
      await navigator.clipboard.writeText(data.sessionCode);
      setCopiedSessionCode(true);
      setTimeout(() => setCopiedSessionCode(false), 3000);
      setBannerSuccess('تم نسخ كود الجلسة السريع! الصقه في موقعك على Vercel ليتم ربط حسابك فوراً.');
      setTimeout(() => setBannerSuccess(null), 5000);
    } catch (err: any) {
      setBannerError(err?.message || 'تعذر نسخ كود الجلسة.');
    }
  };

  const handlePushSessionToVercel = async (e?: React.FormEvent) => {
    if (e) e.preventDefault();
    setPushingToVercel(true);
    setBannerError(null);
    setMagicLoginUrlResult(null);
    try {
      if (targetVercelUrl.trim()) {
        localStorage.setItem(STORAGE_VERCEL_URL_KEY, targetVercelUrl.trim());
      }
      const headers: Record<string, string> = { 'Content-Type': 'application/json' };
      if (accessToken) headers.Authorization = `Bearer ${accessToken}`;
      const res = await fetch('/api/vercel/push-session', {
        method: 'POST',
        headers,
        body: JSON.stringify({
          vercelUrl: targetVercelUrl.trim() || undefined,
          accessToken: accessToken || undefined,
          userEmail: effectiveUserEmail || undefined,
          userName: effectiveUserName || undefined,
          chatId: linkedChatId || personalChatId || undefined,
          sendToTelegram: true,
        }),
      });
      const data = await parseJsonResponse(res, 'تعذر نقل الجلسة إلى Vercel.');
      if (data.sessionCode) {
        await navigator.clipboard.writeText(data.sessionCode).catch(() => {});
      }
      if (data.magicLoginUrl) {
        setMagicLoginUrlResult(data.magicLoginUrl);
      }
      setBannerSuccess(
        data.remoteSynced
          ? 'تم ربط حسابك في Google Drive وتفعيل البوت على موقعك في Vercel مباشرة بنجاح! كما تم إرسال رابط التفعيل إلى تليجرام.'
          : 'تم نسخ كود التفعيل وإرساله إلى محادثتك في تليجرام! الصقه في موقع Vercel لتفعيله فوراً.'
      );
      setTimeout(() => setBannerSuccess(null), 6000);
    } catch (err: any) {
      setBannerError(err?.message || 'حدث خطأ أثناء مزامنة الجلسة مع Vercel.');
    } finally {
      setPushingToVercel(false);
    }
  };

  const handleSignIn = async () => {
    setBannerError(null);
    setUnauthorizedDomainHost(null);
    try {
      const result = await googleSignIn();
      if (result) {
        setAccessToken(result.accessToken);
        await onGoogleAuthenticated(result.accessToken, {
          name: result.user.displayName || undefined,
          email: result.user.email || undefined,
          picture: result.user.photoURL || undefined,
        });
        return;
      }
    } catch (err: any) {
      // Check unauthorized domain FIRST so we never trigger Google's 400: origin_mismatch popup
      if (err?.code === 'auth/unauthorized-domain') {
        if (hasCustomOrEnvClientId && tokenClientRef.current) {
          tokenClientRef.current.requestAccessToken({ prompt: 'select_account' });
          return;
        }
        const currentHost = window.location.hostname;
        setUnauthorizedDomainHost(currentHost);
        setActiveModal('settings');
        setBannerError(
          `النطاق (${currentHost}) غير مضاف بعد في Google Cloud / Firebase. يمكنك الربط فوراً عبر "كود الجلسة السريع" بالأسفل بدون أي إعدادات، أو إضافة النطاق في خطوتين.`
        );
        return;
      }
      if (tokenClientRef.current) {
        tokenClientRef.current.requestAccessToken({ prompt: 'select_account' });
        return;
      }
      if (err?.code !== 'auth/popup-closed-by-user') {
        setBannerError(err?.message || 'تعذر تسجيل الدخول بحساب Google.');
      }
    }
  };

  const handleDisconnectDrive = async () => {
    try {
      await firebaseLogout();
    } catch {
      // Ignore
    }
    clearStoredToken();
    if (accessToken && window.google?.accounts?.oauth2) {
      window.google.accounts.oauth2.revoke(accessToken, () => {});
    }
    setAccessToken(null);
    setUserProfile(null);
    setDriveFiles([]);
    setFolders([]);
    await fetch(`/api/drive/disconnect${buildIdentityQuery()}`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ userEmail: personalEmail, chatId: personalChatId }),
    });
    fetchStatus();
  };

  const handleClearPersonalSession = () => {
    clearStoredToken();
    localStorage.removeItem(STORAGE_EMAIL_KEY);
    localStorage.removeItem(STORAGE_NAME_KEY);
    localStorage.removeItem(STORAGE_CHAT_ID_KEY);
    setPersonalEmail('');
    setPersonalName('');
    setPersonalChatId('');
    setAccessToken(null);
    setUserProfile(null);
    setActiveModal(null);
    setBannerSuccess('تم الخروج من الجلسة المحلية على المتصفح. يمكنك الآن تسجيل الدخول بأي حساب شخصي آخر.');
    setTimeout(() => setBannerSuccess(null), 4000);
  };

  const handleSelectFolder = async (folder: DriveFolder) => {
    if (!accessToken) return;
    try {
      setSelectedFolderId(folder.id);
      setSelectedFolderName(folder.name);
      await syncTokenWithServer(
        accessToken,
        userProfile?.email || personalEmail,
        userProfile?.name || personalName,
        folder.id,
        folder.name
      );
      setBannerSuccess(`تم تحديد المجلد النشط لحسابك: "${folder.name}"`);
      setTimeout(() => setBannerSuccess(null), 3500);
      fetchStatus();
    } catch (err: any) {
      setBannerError(err?.message);
    }
  };

  const handleCreateNewFolder = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!accessToken || !newFolderInput.trim()) return;
    setCreatingFolder(true);
    try {
      const created = await createFolder(accessToken, newFolderInput.trim());
      setFolders((prev) => [created, ...prev]);
      setNewFolderInput('');
      await handleSelectFolder(created);
    } catch (err: any) {
      setBannerError(err?.message || 'فشل إنشاء المجلد الجديد.');
    } finally {
      setCreatingFolder(false);
    }
  };

  const handleToggleAutoCategorize = async () => {
    const nextVal = !autoCategorize;
    setAutoCategorize(nextVal);
    await handleUpdateSettings({ autoCategorize: nextVal });
  };

  const handleToggleSkipDuplicates = async () => {
    const nextVal = !skipDuplicates;
    setSkipDuplicates(nextVal);
    await handleUpdateSettings({ deduplicate: nextVal });
  };

  const triggerBrowserBlobSave = (blobUrl: string, fileName: string) => {
    const a = document.createElement('a');
    a.href = blobUrl;
    a.download = fileName || 'download';
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
  };

  const togglePauseInAppDownload = () => {
    if (!inAppDownload) return;
    if (inAppDownload.status === 'downloading') {
      downloadPausedRef.current = true;
      setInAppDownload((prev) => (prev ? { ...prev, status: 'paused', speedBps: 0 } : null));
    } else if (inAppDownload.status === 'paused') {
      downloadPausedRef.current = false;
      setInAppDownload((prev) => (prev ? { ...prev, status: 'downloading' } : null));
      if (downloadResumeResolverRef.current) {
        const resolve = downloadResumeResolverRef.current;
        downloadResumeResolverRef.current = null;
        resolve();
      }
    }
  };

  const cancelInAppDownload = () => {
    downloadPausedRef.current = false;
    if (downloadResumeResolverRef.current) {
      const resolve = downloadResumeResolverRef.current;
      downloadResumeResolverRef.current = null;
      resolve();
    }
    if (downloadAbortRef.current) {
      downloadAbortRef.current.abort();
      downloadAbortRef.current = null;
    }
    setInAppDownload((prev) => {
      if (prev?.workerJobId) {
        fetch(`/api/media-worker/jobs/${prev.workerJobId}/cancel`, { method: 'POST' }).catch(() => {});
      }
      return prev
        ? {
            ...prev,
            status: 'cancelled',
            speedBps: 0,
          }
        : null;
    });
    setDownloadingItemId(null);
  };

  const startInAppStreamDownload = async (opts: {
    downloadUrl: string;
    fileName: string;
    formatLabel: string;
    compressMode: CompressMode;
    expectedBytes?: number;
    originalBytes?: number;
    itemId?: string;
    requiresWorker?: boolean;
    workerPayload?: {
      url: string;
      sourceUrl?: string;
      format: 'video' | 'audio';
      quality: string;
      durationSec?: number;
    };
  }) => {
    // Cancel any existing active download first
    if (downloadAbortRef.current) {
      downloadAbortRef.current.abort();
    }
    downloadPausedRef.current = false;
    downloadResumeResolverRef.current = null;

    const abortController = new AbortController();
    downloadAbortRef.current = abortController;

    const dlId = opts.itemId || `dl_${Date.now()}`;
    if (opts.itemId) setDownloadingItemId(opts.itemId);
    setBannerError(null);

    const initialTotal = opts.expectedBytes && opts.expectedBytes > 0 ? opts.expectedBytes : 0;
    const initialOriginal = opts.originalBytes && opts.originalBytes > 0 ? opts.originalBytes : initialTotal;

    setInAppDownload({
      id: dlId,
      fileName: opts.fileName,
      formatLabel: opts.formatLabel,
      compressMode: opts.compressMode,
      originalBytes: initialOriginal,
      totalBytes: initialTotal,
      bytesLoaded: 0,
      percent: 0,
      speedBps: 0,
      status: opts.requiresWorker ? 'worker_processing' : 'downloading',
      workerStageLabel: opts.requiresWorker
        ? 'عامل ضغط الفيديو المستقل: جاري بدء مهمة الضغط...'
        : undefined,
    });

    try {
      const headers: Record<string, string> = {};
      if (accessToken) {
        headers.Authorization = `Bearer ${accessToken}`;
      }

      let effectiveDownloadUrl = opts.downloadUrl;

      // Stage A: Decoupled Independent Media Worker (Only when FFmpeg compression is explicitly needed)
      if (opts.requiresWorker && opts.workerPayload) {
        try {
          const startRes = await fetch('/api/media-worker/jobs', {
            method: 'POST',
            headers: { ...headers, 'Content-Type': 'application/json' },
            body: JSON.stringify({
              ...opts.workerPayload,
              compressMode: opts.compressMode,
              fileName: opts.fileName,
              targetBytes: initialTotal,
              originalBytes: initialOriginal,
            }),
            signal: abortController.signal,
          });
          if (startRes.ok) {
            const startData = await startRes.json();
            const wJobId = startData?.job?.id;
            if (wJobId) {
              setInAppDownload((prev) =>
                prev
                  ? {
                      ...prev,
                      workerJobId: wJobId,
                      workerStageLabel: startData.job.stageLabel || 'عامل ضغط الفيديو المستقل...',
                    }
                  : null
              );

              while (!abortController.signal.aborted) {
                await new Promise((r) => setTimeout(r, 500));
                const pollRes = await fetch(`/api/media-worker/jobs/${wJobId}`, {
                  headers,
                  signal: abortController.signal,
                });
                if (!pollRes.ok) {
                  // If serverless instance rotated, fall back gracefully to direct stream
                  break;
                }
                const pollData = await pollRes.json();
                const wJob = pollData?.job;
                if (!wJob) break;

                if (wJob.status === 'completed' && wJob.downloadUrl) {
                  effectiveDownloadUrl = wJob.downloadUrl;
                  break;
                }
                if (wJob.status === 'failed') {
                  throw new Error(wJob.errorMessage || 'تعذر إكمال ضغط الفيديو في عامل المعالجة المستقل.');
                }
                if (wJob.status === 'cancelled') {
                  throw new Error('AbortError');
                }

                setInAppDownload((prev) =>
                  prev && prev.status !== 'cancelled'
                    ? {
                        ...prev,
                        status: 'worker_processing',
                        percent: Math.min(99, Number(wJob.progress) || 0),
                        workerStageLabel:
                          wJob.stageLabel || 'عامل ضغط الفيديو المستقل: جاري تقليص الحجم...',
                      }
                    : prev
                );
              }
            }
          }
        } catch (workerErr: any) {
          if (
            workerErr?.name === 'AbortError' ||
            workerErr?.message === 'AbortError' ||
            abortController.signal.aborted
          ) {
            throw workerErr;
          }
          console.warn('Independent worker fallback to direct stream:', workerErr?.message);
        }
      }

      // Stage B: Fast Direct Streaming Download
      setInAppDownload((prev) =>
        prev && prev.status !== 'cancelled'
          ? {
              ...prev,
              status: 'downloading',
              workerStageLabel: undefined,
            }
          : prev
      );

      const res = await fetch(effectiveDownloadUrl, {
        headers,
        signal: abortController.signal,
      });

      const contentType = (res.headers.get('content-type') || '').toLowerCase();
      if (!res.ok || contentType.includes('application/json') || contentType.includes('text/html')) {
        let errMsg = 'تعذر تحميل الملف المباشر.';
        try {
          const errJson = await res.json();
          if (errJson?.error) errMsg = errJson.error;
        } catch {
          // Ignore parse error
        }
        throw new Error(errMsg);
      }

      const contentLengthHeader = Number(res.headers.get('content-length') || 0);
      const xOriginalSizeHeader = Number(res.headers.get('x-original-size') || 0);
      const totalBytes = contentLengthHeader > 0 ? contentLengthHeader : initialTotal;
      const originalBytes =
        initialOriginal > 0 ? initialOriginal : xOriginalSizeHeader > 0 ? xOriginalSizeHeader : totalBytes;

      setInAppDownload((prev) =>
        prev
          ? {
              ...prev,
              totalBytes,
              originalBytes,
            }
          : null
      );

      if (!res.body) {
        const blob = await res.blob();
        const blobUrl = URL.createObjectURL(blob);
        triggerBrowserBlobSave(blobUrl, opts.fileName);
        setInAppDownload((prev) =>
          prev
            ? {
                ...prev,
                bytesLoaded: blob.size,
                totalBytes: blob.size,
                percent: 100,
                speedBps: 0,
                status: 'completed',
                blobUrl,
              }
            : null
        );
        return;
      }

      const reader = res.body.getReader();
      const chunks: BlobPart[] = [];
      let receivedBytes = 0;
      let lastTickTime = Date.now();
      let bytesSinceLastTick = 0;
      let currentSpeedBps = 0;

      while (true) {
        if (downloadPausedRef.current) {
          await new Promise<void>((resolve) => {
            downloadResumeResolverRef.current = resolve;
          });
        }

        const { done, value } = await reader.read();
        if (done) break;

        if (value) {
          chunks.push(value as unknown as BlobPart);
          receivedBytes += value.byteLength;
          bytesSinceLastTick += value.byteLength;

          const now = Date.now();
          const elapsedMs = now - lastTickTime;
          if (elapsedMs >= 200) {
            currentSpeedBps = Math.round((bytesSinceLastTick * 1000) / elapsedMs);
            lastTickTime = now;
            bytesSinceLastTick = 0;

            const effectiveTotal = totalBytes > 0 ? totalBytes : receivedBytes;
            const displayedLoaded =
              totalBytes > 0 ? Math.min(receivedBytes, totalBytes) : receivedBytes;
            const pct =
              effectiveTotal > 0
                ? Math.min(99, Math.round((displayedLoaded / effectiveTotal) * 100))
                : Math.min(95, Math.round((receivedBytes / (5 * 1024 * 1024)) * 100));

            setInAppDownload((prev) =>
              prev && prev.status !== 'cancelled'
                ? {
                    ...prev,
                    bytesLoaded: displayedLoaded,
                    totalBytes: effectiveTotal,
                    percent: pct,
                    speedBps: currentSpeedBps,
                  }
                : prev
            );
          }
        }
      }

      const finalMime =
        opts.fileName.endsWith('.zip')
          ? 'application/zip'
          : opts.fileName.endsWith('.mp3')
            ? 'audio/mpeg'
            : opts.fileName.endsWith('.mp4')
              ? 'video/mp4'
              : res.headers.get('content-type') || 'application/octet-stream';

      const blob = new Blob(chunks, { type: finalMime });
      const blobUrl = URL.createObjectURL(blob);

      setInAppDownload((prev) =>
        prev
          ? {
              ...prev,
              bytesLoaded: blob.size,
              totalBytes: blob.size,
              percent: 100,
              speedBps: 0,
              status: 'completed',
              blobUrl,
            }
          : null
      );

      triggerBrowserBlobSave(blobUrl, opts.fileName);
      setBannerSuccess(`اكتمل تحميل "${opts.fileName}" (${formatBytes(blob.size)}) بنجاح!`);
      setTimeout(() => setBannerSuccess(null), 5000);

      // Register completed device download in transfer history with totalBytes
      try {
        await fetch('/api/transfers/register-web', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            fileName: opts.fileName,
            mimeType: finalMime,
            totalBytes: blob.size,
            sizeBytes: blob.size,
            direction: 'to_device',
            sourceType: 'direct_url',
            compressMode: opts.compressMode,
            mediaFormat: opts.fileName.endsWith('.mp3') ? 'audio' : 'video',
            quality: externalQuality,
            userEmail: personalEmail || undefined,
            chatId: personalChatId || undefined,
          }),
        });
        fetchStatus();
      } catch {
        // Ignore history registration error
      }
    } catch (err: any) {
      if (err?.name === 'AbortError' || abortController.signal.aborted) {
        setInAppDownload((prev) => (prev ? { ...prev, status: 'cancelled', speedBps: 0 } : null));
      } else {
        const msg = err?.message || 'حدث خطأ أثناء تحميل الملف إلى جهازك.';
        setInAppDownload((prev) =>
          prev ? { ...prev, status: 'failed', speedBps: 0, errorMessage: msg } : null
        );
        setBannerError(msg);
      }
    } finally {
      setDownloadingItemId(null);
      if (downloadAbortRef.current === abortController) {
        downloadAbortRef.current = null;
      }
    }
  };

  const handleAuthenticatedProxyDownload = async (
    proxyUrl: string,
    fallbackFileName: string,
    itemId: string
  ) => {
    await startInAppStreamDownload({
      downloadUrl: proxyUrl,
      fileName: fallbackFileName,
      formatLabel: fallbackFileName.endsWith('.zip') ? 'مضغوط ZIP' : 'ملف مباشر',
      compressMode: fallbackFileName.endsWith('.zip') ? 'zip' : 'none',
      itemId,
    });
  };

  const inspectUrlFormats = useCallback(
    async (rawUrl: string, fmtOverride?: 'video' | 'audio', qOverride?: string, compOverride?: CompressMode) => {
      const clean = rawUrl.trim();
      if (!clean || !/^https?:\/\//i.test(clean)) return null;

      setInspectingUrl(true);
      setBannerError(null);
      lastInspectedUrlRef.current = clean;

      try {
        const headers: Record<string, string> = { 'Content-Type': 'application/json' };
        if (accessToken) {
          headers.Authorization = `Bearer ${accessToken}`;
        }
        const res = await fetch('/api/transfers/resolve-direct', {
          method: 'POST',
          headers,
          body: JSON.stringify({
            url: clean,
            mediaFormat: fmtOverride || 'video',
            quality: qOverride || '720',
            compressMode: compOverride || 'none',
            userEmail: personalEmail || undefined,
            targetChatId: personalChatId || undefined,
          }),
        });
        const data = await parseJsonResponse<ResolvedMediaInfo>(
          res,
          'تعذر استخراج معلومات الرابط والصيغ المتاحة.'
        );
        setResolvedMediaInfo(data);
        if (!data.zipEligible || data.isVideoPlatform) {
          setExternalCompressMode('none');
        }
        return data;
      } catch (err: any) {
        lastInspectedUrlRef.current = '';
        setBannerError(err?.message || 'حدث خطأ أثناء فحص الرابط واستخراج الصيغ.');
        return null;
      } finally {
        setInspectingUrl(false);
      }
    },
    [accessToken, personalEmail, personalChatId]
  );

  // Automatically inspect URL and display formats & sizes as soon as a valid link is pasted or typed
  useEffect(() => {
    const trimmed = externalUrlInput.trim();
    if (!trimmed || !/^https?:\/\/\S+\.\S+/i.test(trimmed)) {
      if (!trimmed) {
        setResolvedMediaInfo(null);
        lastInspectedUrlRef.current = '';
      }
      return;
    }
    if (trimmed === lastInspectedUrlRef.current) {
      return;
    }
    const timer = setTimeout(() => {
      inspectUrlFormats(trimmed);
    }, 300);
    return () => clearTimeout(timer);
  }, [externalUrlInput, inspectUrlFormats]);

  const handlePasteFromClipboard = async () => {
    setBannerError(null);
    try {
      const text = await navigator.clipboard.readText();
      if (text && text.trim()) {
        const clean = text.trim();
        setExternalUrlInput(clean);
        if (/^https?:\/\//i.test(clean)) {
          await inspectUrlFormats(clean);
        }
      }
    } catch {
      setBannerError('يرجى اللصق يدوياً داخل حقل الرابط أو السماح بصلاحية الحافظة.');
    }
  };

  const getEffectiveFormatBytes = useCallback(
    (fmtOrBytes: AvailableMediaFormat | number | null | undefined, mode: CompressMode = externalCompressMode) => {
      if (!fmtOrBytes) return 0;
      if (typeof fmtOrBytes === 'object') {
        if (mode === 'zip') {
          return fmtOrBytes.zipCompressedBytes || Math.max(32 * 1024, Math.round(fmtOrBytes.sizeBytes * 0.985));
        }
        if (mode === 'media') {
          return fmtOrBytes.mediaCompressedBytes || Math.max(32 * 1024, Math.round(fmtOrBytes.sizeBytes * 0.65));
        }
        return fmtOrBytes.sizeBytes;
      }
      if (fmtOrBytes <= 0) return 0;
      if (mode === 'zip') return Math.max(32 * 1024, Math.round(fmtOrBytes * 0.985));
      if (mode === 'media') return Math.max(32 * 1024, Math.round(fmtOrBytes * 0.65));
      return fmtOrBytes;
    },
    [externalCompressMode]
  );

  const buildFormatDownloadParams = useCallback(
    (
      fmt: AvailableMediaFormat,
      mode: CompressMode,
      rawCustomName: string,
      baselineOriginalBytes: number
    ) => {
      const canUseLosslessZip = Boolean(
        resolvedMediaInfo?.zipEligible && (resolvedMediaInfo?.zipSavedPercent || 0) >= 10
      );
      const effectiveCompress: CompressMode =
        mode === 'zip' && canUseLosslessZip ? 'zip' : 'none';
      const effectiveBytes = getEffectiveFormatBytes(fmt, effectiveCompress);
      const isZip = effectiveCompress === 'zip';

      const cleanCustom =
        rawCustomName.trim() &&
        !/^https?:\/\//i.test(rawCustomName.trim()) &&
        !/youtu\.?be|tiktok\.com|t\.me|drive\.google/i.test(rawCustomName.trim())
          ? rawCustomName.trim().replace(/\.[^/.]+$/, '')
          : '';

      const targetFileName = cleanCustom
        ? `${cleanCustom}.${isZip ? `${fmt.ext}.zip` : fmt.ext}`
        : isZip
          ? fmt.zipFileName
          : fmt.fileName;

      const baseUrl = isZip ? fmt.zipDownloadUrl : fmt.downloadUrl;
      let finalUrl = baseUrl;
      try {
        const parsed = new URL(baseUrl, window.location.origin);
        parsed.pathname = `/api/direct-download/${encodeURIComponent(targetFileName)}`;
        parsed.searchParams.set('name', targetFileName);
        parsed.searchParams.set('compress', effectiveCompress);
        if (effectiveBytes > 0) {
          parsed.searchParams.set('targetBytes', String(effectiveBytes));
        }
        if (baselineOriginalBytes > 0) {
          parsed.searchParams.set('origBytes', String(baselineOriginalBytes));
        }
        finalUrl = `${parsed.pathname}${parsed.search}`;
      } catch {
        // Fallback to baseUrl if URL parsing fails
      }

      const formatLabel = isZip
        ? `${fmt.label} (ZIP)`
        : mode === 'media'
          ? `${fmt.label} (مقلّص)`
          : fmt.label;

      // Only invoke the independent FFmpeg worker when explicitly needed for media compression or compact audio
      const requiresWorker =
        mode === 'media'
          ? Boolean(fmt.requiresWorkerForMedia)
          : mode === 'none'
            ? Boolean(fmt.requiresWorkerForOriginal)
            : false;

      return {
        downloadUrl: finalUrl,
        fileName: targetFileName,
        formatLabel,
        compressMode: effectiveCompress,
        expectedBytes: effectiveBytes,
        originalBytes: baselineOriginalBytes || fmt.sizeBytes,
        requiresWorker,
        workerPayload: {
          url: externalUrlInput.trim(),
          sourceUrl: mode === 'media' ? fmt.mediaStreamUrl || fmt.sourceStreamUrl : fmt.sourceStreamUrl,
          format: fmt.format,
          quality: fmt.quality,
          durationSec: resolvedMediaInfo?.durationSec || 0,
        },
      };
    },
    [getEffectiveFormatBytes, externalUrlInput, resolvedMediaInfo]
  );

  const handleUrlUploadSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!externalUrlInput.trim()) return;

    setSubmittingUrl(true);
    setBannerError(null);
    setLastDirectDownload(null);

    const rawCustom = externalCustomName.trim();
    const safeCustomName =
      rawCustom && !/^https?:\/\//i.test(rawCustom) && !/youtu\.?be|tiktok\.com|t\.me|drive\.google/i.test(rawCustom)
        ? rawCustom
        : undefined;

    if (externalDestination === 'device') {
      try {
        let info = resolvedMediaInfo;
        if (!info || lastInspectedUrlRef.current !== externalUrlInput.trim()) {
          info = await inspectUrlFormats(externalUrlInput.trim());
        }
        if (!info) {
          setSubmittingUrl(false);
          return;
        }

        // Find matching format from availableFormats based on user's selected format & quality
        const matchedFmt =
          info.availableFormats.find(
            (f) => f.format === externalMediaFormat && f.quality === externalQuality
          ) ||
          info.availableFormats.find((f) => f.format === externalMediaFormat) ||
          info.availableFormats[0];

        // Release submit button spinner as soon as in-app download card takes over
        setSubmittingUrl(false);

        if (matchedFmt) {
          const dlParams = buildFormatDownloadParams(
            matchedFmt,
            externalCompressMode,
            externalCustomName,
            info.originalSizeBytes || matchedFmt.sizeBytes
          );
          void startInAppStreamDownload(dlParams);
        } else {
          const fallbackBytes = getEffectiveFormatBytes(
            info.compressedSizeBytes || info.sizeBytes,
            externalCompressMode
          );
          void startInAppStreamDownload({
            downloadUrl: info.proxyDownloadUrl,
            fileName: info.fileName,
            formatLabel: externalMediaFormat === 'audio' ? `MP3 • ${externalQuality}kbps` : `MP4 • ${externalQuality}p`,
            compressMode: externalCompressMode,
            expectedBytes: fallbackBytes,
            originalBytes: info.originalSizeBytes || info.sizeBytes,
          });
        }
      } catch (err: any) {
        setBannerError(err?.message || 'حدث خطأ أثناء بدء التحميل المباشر.');
        setSubmittingUrl(false);
      }
      return;
    }

    try {
      const headers: Record<string, string> = { 'Content-Type': 'application/json' };
      if (accessToken) {
        headers.Authorization = `Bearer ${accessToken}`;
      }
      const matchedFmt =
        resolvedMediaInfo?.availableFormats?.find(
          (f) => f.format === externalMediaFormat && f.quality === externalQuality
        ) || resolvedMediaInfo?.availableFormats?.find((f) => f.format === externalMediaFormat);
      const targetBytesForJob = matchedFmt
        ? getEffectiveFormatBytes(matchedFmt, externalCompressMode)
        : undefined;

      const res = await fetch('/api/transfers/url', {
        method: 'POST',
        headers,
        body: JSON.stringify({
          url: externalUrlInput.trim(),
          customFileName: safeCustomName,
          destination: externalDestination,
          mediaFormat: externalMediaFormat,
          quality: externalQuality,
          compressMode: externalCompressMode,
          targetBytes: targetBytesForJob,
          durationSec: resolvedMediaInfo?.durationSec || undefined,
          userEmail: personalEmail || undefined,
          targetChatId: personalChatId || undefined,
        }),
      });
      await parseJsonResponse(res, 'تعذر إضافة الرابط للتحويل.');
      setExternalUrlInput('');
      setExternalCustomName('');
      setResolvedMediaInfo(null);
      lastInspectedUrlRef.current = '';
      setBannerSuccess(
        externalDestination === 'telegram'
          ? 'تم بدء سحب الرابط بالصيغة والحجم المختارين وإرساله إلى محادثتك في تليجرام!'
          : 'تمت إضافة الرابط بالصيغة والحجم المختارين لطابور الرفع إلى Google Drive!'
      );
      setTimeout(() => setBannerSuccess(null), 4000);
      fetchStatus();
    } catch (err: any) {
      setBannerError(err?.message || 'حدث خطأ أثناء معالجة الرابط.');
    } finally {
      setSubmittingUrl(false);
    }
  };

  const handleSendDriveFileToTelegram = async (file: DriveFile) => {
    setSendingDriveFileId(file.id);
    setBannerError(null);
    try {
      const headers: Record<string, string> = { 'Content-Type': 'application/json' };
      if (accessToken) {
        headers.Authorization = `Bearer ${accessToken}`;
      }
      const res = await fetch('/api/telegram/send-drive-file', {
        method: 'POST',
        headers,
        body: JSON.stringify({
          driveFileId: file.id,
          fileName: file.name,
          mimeType: file.mimeType,
          size: file.size,
          userEmail: personalEmail || undefined,
          targetChatId: personalChatId || undefined,
        }),
      });
      const data = await parseJsonResponse(res, 'تعذر إرسال الملف إلى تليجرام.');
      setBannerSuccess(`جاري سحب الملف "${file.name}" من حسابك في Google Drive وإرساله إلى تليجرام!`);
      setTimeout(() => setBannerSuccess(null), 4000);
      fetchStatus();
    } catch (err: any) {
      setBannerError(err?.message || 'تعذر إرسال الملف إلى تليجرام.');
    } finally {
      setSendingDriveFileId(null);
    }
  };

  const handleUpdateSettings = async (payload: Record<string, any>) => {
    setSavingSettings(true);
    setBannerError(null);
    try {
      const res = await fetch('/api/admin/settings', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          userEmail: personalEmail || undefined,
          chatId: personalChatId || undefined,
          ...payload,
        }),
      });
      await parseJsonResponse(res, 'تعذر حفظ الإعدادات.');
      await fetchStatus();
      setBannerSuccess('تم حفظ وتطبيق الإعدادات بنجاح!');
      setTimeout(() => setBannerSuccess(null), 3000);
    } catch (err: any) {
      setBannerError(err?.message || 'حدث خطأ أثناء تحديث الإعدادات.');
    } finally {
      setSavingSettings(false);
    }
  };

  const handleCancelJob = async (jobId: string) => {
    try {
      await fetch(`/api/transfers/${jobId}/cancel`, { method: 'POST' });
      fetchStatus();
    } catch {
      // Ignore
    }
  };

  const handleCancelAllJobs = async (scope: 'personal' | 'all' = 'personal') => {
    try {
      await fetch('/api/transfers/cancel-all', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          userEmail: personalEmail || undefined,
          chatId: personalChatId || undefined,
          scope,
        }),
      });
      setBannerSuccess('تم إلغاء العمليات الجارية بنجاح.');
      setTimeout(() => setBannerSuccess(null), 3500);
      fetchStatus();
    } catch {
      // Ignore
    }
  };

  const handleDeleteJob = async (jobId: string) => {
    try {
      await fetch(`/api/transfers/${jobId}`, { method: 'DELETE' });
      fetchStatus();
    } catch {
      // Ignore
    }
  };

  const handleClearFailedJobs = async () => {
    setClearingFailed(true);
    try {
      const res = await fetch(`/api/transfers/failed/clear${buildIdentityQuery()}`, { method: 'DELETE' });
      const data = await parseJsonResponse(res, 'تعذر تنظيف العمليات الفاشلة.');
      setBannerSuccess(`تم حذف ${data.removedCount} من الملفات الفاشلة والملغاة من سجلك.`);
      setTimeout(() => setBannerSuccess(null), 3500);
      fetchStatus();
    } catch {
      // Ignore
    } finally {
      setClearingFailed(false);
    }
  };

  const handleDirectLargeFileUpload = async (e: React.ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0];
    if (!file || !accessToken) return;

    setUploadingLocal(true);
    setLocalUploadProgress(0);
    setLocalUploadFileName(file.name);
    setBannerError(null);

    try {
      const targetFolder = selectedFolderId || serverStatus?.drive.activeFolderId || undefined;
      const sessionUri = await startResumableUpload(accessToken, file, targetFolder);

      const CHUNK_SIZE = 10 * 1024 * 1024; // 10MB chunks
      let offset = 0;
      let finalDriveResponse: any = null;

      while (offset < file.size) {
        const end = Math.min(offset + CHUNK_SIZE, file.size);
        const chunk = file.slice(offset, end);
        const result = await uploadChunk(sessionUri, chunk, offset, file.size);
        offset = end;
        setLocalUploadProgress(Math.round((offset / file.size) * 100));
        if (result.done) {
          finalDriveResponse = result.data;
        }
      }

      await fetch('/api/transfers/register-web', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          userEmail: personalEmail || undefined,
          chatId: personalChatId || undefined,
          fileName: file.name,
          mimeType: file.type || 'application/octet-stream',
          totalBytes: file.size,
          driveFileId: finalDriveResponse?.id,
          webViewLink: finalDriveResponse?.webViewLink,
          folderName: selectedFolderName,
        }),
      });

      setBannerSuccess(`تم رفع الملف الضخم "${file.name}" إلى حسابك في Google Drive بنجاح!`);
      setTimeout(() => setBannerSuccess(null), 5000);
      await refreshDriveFoldersAndFiles();
      fetchStatus();
    } catch (err: any) {
      setBannerError(err?.message || 'فشل رفع الملف المحلي إلى Google Drive.');
    } finally {
      setUploadingLocal(false);
      setLocalUploadFileName('');
      e.target.value = '';
    }
  };

  const handleReconnectBot = async () => {
    setReconnectingBot(true);
    try {
      await fetch('/api/bot/reconnect', { method: 'POST' });
      await fetchStatus();
    } finally {
      setReconnectingBot(false);
    }
  };

  const handleActivateVercelWebhook = async () => {
    setReconnectingBot(true);
    setBannerError(null);
    try {
      const res = await fetch('/api/bot/webhook', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ origin: window.location.origin }),
      });
      const data = await parseJsonResponse(res, 'تعذر تفعيل Webhook.');
      setBannerSuccess(`تم تفعيل Webhook البوت بنجاح على الرابط: ${data.webhookUrl}`);
      setTimeout(() => setBannerSuccess(null), 5000);
      await fetchStatus();
    } catch (err: any) {
      setBannerError(err?.message || 'حدث خطأ أثناء تفعيل Webhook.');
    } finally {
      setReconnectingBot(false);
    }
  };

  const handleRetryJob = async (jobId: string) => {
    await fetch(`/api/transfers/${jobId}/retry`, { method: 'POST' });
    fetchStatus();
  };

  const handleDeleteDriveFile = async (fileId: string) => {
    if (!accessToken) return;
    try {
      await deleteFile(accessToken, fileId);
      setDriveFiles((prev) => prev.filter((f) => f.id !== fileId));
      setConfirmDeleteId(null);
    } catch (err: any) {
      setBannerError(err?.message || 'تعذر حذف الملف.');
    }
  };

  const copyLink = (id: string, link?: string) => {
    const url = link || `https://drive.google.com/file/d/${id}/view`;
    navigator.clipboard.writeText(url);
    setCopiedId(id);
    setTimeout(() => setCopiedId(null), 2000);
  };

  const formatBytes = (bytes?: string | number) => {
    if (bytes === undefined || bytes === null) return '0 B';
    const b = typeof bytes === 'string' ? parseInt(bytes, 10) : bytes;
    if (isNaN(b) || b === 0) return '0 B';
    const k = 1024;
    const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];
    const i = Math.floor(Math.log(b) / Math.log(k));
    return `${parseFloat((b / Math.pow(k, i)).toFixed(2))} ${sizes[i]}`;
  };

  const filteredDriveFiles = driveFiles.filter((f) =>
    f.name.toLowerCase().includes(searchQuery.toLowerCase())
  );

  const botConnected = serverStatus?.bot.connected ?? false;
  const mtprotoConnected = serverStatus?.bot.mtproto?.connected ?? false;
  const driveConnected = Boolean(accessToken) || (serverStatus?.drive.connected ?? false);
  const effectiveUserEmail = userProfile?.email || serverStatus?.drive.userEmail || personalEmail || null;
  const effectiveUserName = userProfile?.name || serverStatus?.drive.userName || personalName || null;
  const linkCode = serverStatus?.drive.linkCode || '';
  const linkedChatId = serverStatus?.drive.linkedChatId || (personalChatId ? Number(personalChatId) : null);
  const botUsername = serverStatus?.bot.info?.username || '';
  const telegramDeepLink =
    botUsername && linkCode ? `https://t.me/${botUsername}?start=link_${linkCode}` : botUsername ? `https://t.me/${botUsername}` : '';

  const selectedResolvedFormatObj = resolvedMediaInfo?.availableFormats?.find(
    (f) => f.format === externalMediaFormat && f.quality === externalQuality
  ) || resolvedMediaInfo?.availableFormats?.find((f) => f.format === externalMediaFormat);

  const selectedEffectiveBytes = selectedResolvedFormatObj
    ? getEffectiveFormatBytes(selectedResolvedFormatObj, externalCompressMode)
    : getEffectiveFormatBytes(
        resolvedMediaInfo?.compressedSizeBytes || resolvedMediaInfo?.sizeBytes || 0,
        externalCompressMode
      );

  const selectedOriginalBytes =
    resolvedMediaInfo?.originalSizeBytes || selectedResolvedFormatObj?.sizeBytes || 0;

  const selectedSavedBytes =
    selectedOriginalBytes > selectedEffectiveBytes && selectedEffectiveBytes > 0
      ? selectedOriginalBytes - selectedEffectiveBytes
      : 0;

  const selectedSavedPercent =
    selectedOriginalBytes > 0 && selectedSavedBytes > 0
      ? Math.round((selectedSavedBytes / selectedOriginalBytes) * 100)
      : 0;

  const handleInstallButtonClick = async () => {
    if (isInstallable) {
      const accepted = await triggerPwaInstall();
      if (accepted) {
        setBannerSuccess('تم تثبيت التطبيق على شاشة هاتفك بنجاح!');
        setTimeout(() => setBannerSuccess(null), 4000);
        return;
      }
    }
    setActiveModal('pwa_install');
  };

  const videoQualityPresets = [
    { q: '1080', title: '1080p Full HD', desc: 'أعلى دقة ووضوح' },
    { q: '720', title: '720p HD', desc: 'جودة عالية متوازنة' },
    { q: '480', title: '480p SD', desc: 'حجم متوسط (~70% توفير)' },
    { q: '360', title: '360p خفيف', desc: 'سريع (~81% توفير)' },
    { q: '240', title: '240p اقتصادي', desc: 'أقل بيانات (~88% توفير)' },
  ];

  const audioQualityPresets = [
    { q: '320', title: '320kbps فائق', desc: 'أعلى نقاء صوتي' },
    { q: '192', title: '192kbps متوازن', desc: 'جودة ممتازة وحجم مناسب' },
    { q: '128', title: '128kbps خفيف', desc: 'أصغر حجم صوتي (~94% توفير)' },
  ];

  return (
    <div dir="rtl" className="min-h-screen w-full max-w-full overflow-x-hidden bg-[#090D16] text-slate-100 font-sans flex flex-col">
      {/* Sticky Top App Bar — Clean 3-Zone Mobile & Desktop Contract */}
      <header className="w-full px-4 sm:px-6 py-3 border-b border-slate-800/80 bg-[#0D1322]/95 backdrop-blur-md sticky top-0 z-30">
        <div className="max-w-5xl mx-auto flex items-center justify-between gap-4">
          {/* Zone 1: Brand Wordmark */}
          <a href="/" className="text-base sm:text-lg font-bold text-white tracking-tight whitespace-nowrap shrink-0">
            TeleDrive Cloud
          </a>

          {/* Zone 2: Quick Navigation Links (Desktop) */}
          <nav className="hidden md:flex items-center gap-6 text-xs font-medium text-slate-300">
            <button
              type="button"
              onClick={() => setActiveModal('settings')}
              className="hover:text-white transition-colors whitespace-nowrap shrink-0 cursor-pointer"
            >
              إعدادات الحساب والربط
            </button>
            <button
              type="button"
              onClick={() => {
                setActiveModal('drive_files');
                if (accessToken) refreshDriveFoldersAndFiles();
              }}
              className="hover:text-white transition-colors whitespace-nowrap shrink-0 cursor-pointer"
            >
              ملفاتي في Drive
            </button>
            <button
              type="button"
              onClick={() => setActiveModal('large_upload')}
              className="hover:text-white transition-colors whitespace-nowrap shrink-0 cursor-pointer"
            >
              رفع ملف ضخم
            </button>
            <button
              type="button"
              onClick={() => setActiveModal('admin')}
              className="hover:text-white transition-colors whitespace-nowrap shrink-0 cursor-pointer"
            >
              إدارة البوت
            </button>
          </nav>

          {/* Zone 3: Primary Actions (Install App + Menu) */}
          <div className="flex items-center gap-2 shrink-0">
            {!isInstalled && (
              <button
                type="button"
                onClick={handleInstallButtonClick}
                className="min-h-[40px] px-3 sm:px-3.5 py-2 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap shrink-0 shadow-sm"
              >
                <Smartphone className="w-3.5 h-3.5 shrink-0" />
                <span>تثبيت التطبيق</span>
              </button>
            )}

            <button
              type="button"
              onClick={() => setActiveModal('menu')}
              className="min-h-[40px] px-3.5 py-2 rounded-xl bg-sky-600 hover:bg-sky-500 text-white text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap shrink-0 shadow-sm"
            >
              <Menu className="w-4 h-4 shrink-0" />
              <span>القائمة</span>
            </button>
          </div>
        </div>
      </header>

      {/* Offline Connectivity Banner */}
      {!isOnline && (
        <div className="w-full bg-amber-950/90 border-b border-amber-500/40 px-4 py-2 text-center text-xs text-amber-200 flex items-center justify-center gap-2">
          <WifiOff className="w-3.5 h-3.5 text-amber-400 shrink-0" />
          <span>أنت الآن في وضع عدم الاتصال بالإنترنت — يتم عرض الواجهة المخزنة محلياً.</span>
        </div>
      )}

      {/* Main Workspace */}
      <main className="flex-1 w-full max-w-5xl mx-auto px-3.5 sm:px-6 py-4 sm:py-6 space-y-5">
        {/* Notification Banners */}
        {bannerError && (
          <div className="p-3.5 rounded-xl bg-rose-950/70 border border-rose-500/40 text-rose-200 flex items-center justify-between gap-3">
            <div className="flex items-center gap-2.5 text-xs sm:text-sm min-w-0">
              <AlertTriangle className="w-4 h-4 text-rose-400 shrink-0" />
              <span className="break-words">{bannerError}</span>
            </div>
            <button
              onClick={() => setBannerError(null)}
              className="min-h-[36px] px-2.5 text-xs text-rose-300 hover:text-white shrink-0 cursor-pointer"
            >
              إغلاق
            </button>
          </div>
        )}

        {bannerSuccess && (
          <div className="p-3.5 rounded-xl bg-emerald-950/70 border border-emerald-500/40 text-emerald-200 flex flex-wrap items-center justify-between gap-3">
            <div className="flex items-center gap-2.5 text-xs sm:text-sm min-w-0">
              <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0" />
              <span className="break-words">{bannerSuccess}</span>
            </div>
            <div className="flex items-center gap-2 shrink-0">
              {lastDirectDownload && (
                <a
                  href={lastDirectDownload.url}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="px-3 py-1.5 rounded-lg bg-emerald-600 hover:bg-emerald-500 text-white text-xs font-bold flex items-center gap-1.5 whitespace-nowrap"
                >
                  <Download className="w-3.5 h-3.5" />
                  <span>تنزيل مباشر</span>
                </a>
              )}
              <button
                onClick={() => {
                  setBannerSuccess(null);
                  setLastDirectDownload(null);
                }}
                className="min-h-[36px] px-2.5 text-xs text-emerald-300 hover:text-white cursor-pointer"
              >
                إغلاق
              </button>
            </div>
          </div>
        )}

        {/* Clean Unboxed Account & Status Bar */}
        <div className="w-full px-4 py-3 rounded-2xl bg-[#0F1626] border border-slate-800/80 flex flex-wrap items-center justify-between gap-3 text-xs text-slate-400">
          <div className="flex flex-wrap items-center gap-x-2.5 gap-y-1 min-w-0">
            <button
              type="button"
              onClick={() => setActiveModal('settings')}
              className={`font-semibold hover:underline cursor-pointer ${
                driveConnected ? 'text-emerald-400' : 'text-amber-400'
              }`}
            >
              {driveConnected
                ? `حساب Drive: ${effectiveUserEmail || effectiveUserName}`
                : 'اضغط لربط حساب Google Drive وتليجرام'}
            </button>
            <span aria-hidden="true">·</span>
            <span className="truncate">
              المجلد: <strong className="text-slate-200 font-medium">{serverStatus?.drive.activeFolderName || selectedFolderName}</strong>
            </span>
            <span aria-hidden="true">·</span>
            <span>
              تليجرام: <strong className="text-slate-200 font-medium">{linkedChatId ? `مربوط (#${linkedChatId})` : 'غير مربوط'}</strong>
            </span>
          </div>

          <div className="flex items-center gap-2.5 tabular-nums text-slate-300">
            <span>المكتملة: {serverStatus?.stats.completedJobs ?? 0}</span>
            <span aria-hidden="true">·</span>
            <span>الجارية: {serverStatus?.stats.activeJobs ?? 0}</span>
            <span aria-hidden="true">·</span>
            <span dir="ltr">{formatBytes(serverStatus?.stats.totalBytesTransferred ?? 0)}</span>
          </div>
        </div>

        {/* =====================================================================
            CORE CARD 1: PASTE LINK -> DIRECT INLINE FORMAT, RESOLUTION & SIZE
           ===================================================================== */}
        <section className="w-full bg-[#0F1626] border border-slate-800/90 rounded-2xl p-4 sm:p-6 space-y-5 shadow-lg">
          <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-2 border-b border-slate-800/70 pb-3.5">
            <div>
              <h1 className="text-base sm:text-xl font-bold text-white tracking-tight">
                سحب وتحميل الفيديوهات والملفات عبر الروابط
              </h1>
              <p className="text-xs text-slate-400 mt-1">
                الصق رابط YouTube أو TikTok أو Google Drive أو MediaFire واختر الصيغة والدقة والحجم مباشرة بالأسفل
              </p>
            </div>
            {inspectingUrl && (
              <div className="flex items-center gap-2 text-xs text-sky-400 font-medium shrink-0">
                <Loader2 className="w-4 h-4 animate-spin" />
                <span>جاري فحص الرابط وحساب الأحجام...</span>
              </div>
            )}
          </div>

          <form onSubmit={handleUrlUploadSubmit} className="space-y-5">
            {/* STEP 1: URL Input with 1-Tap Paste & Auto-Detection */}
            <div className="space-y-2">
              <div className="flex items-center justify-between gap-2">
                <label className="text-xs font-semibold text-slate-200">
                  1. الصق رابط الفيديو أو الملف هنا
                </label>
                {externalUrlInput.trim() && (
                  <button
                    type="button"
                    onClick={() => inspectUrlFormats(externalUrlInput)}
                    disabled={inspectingUrl}
                    className="text-xs text-sky-400 hover:text-sky-300 font-medium flex items-center gap-1 cursor-pointer disabled:opacity-50"
                  >
                    <RefreshCw className={`w-3 h-3 ${inspectingUrl ? 'animate-spin' : ''}`} />
                    <span>تحديث فحص الصيغ والأحجام</span>
                  </button>
                )}
              </div>

              <div className="flex flex-col sm:flex-row gap-2">
                <div className="relative flex-1 flex items-center">
                  <input
                    type="text"
                    required
                    dir="ltr"
                    value={externalUrlInput}
                    onChange={(e) => setExternalUrlInput(e.target.value)}
                    onPaste={(e) => {
                      const pasted = e.clipboardData?.getData('text')?.trim();
                      if (pasted && /^https?:\/\//i.test(pasted)) {
                        setTimeout(() => inspectUrlFormats(pasted), 50);
                      }
                    }}
                    placeholder="https://youtube.com/watch?v=... أو رابط TikTok / Drive / MediaFire..."
                    className="w-full min-h-[46px] pl-3.5 pr-10 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-sm text-white placeholder-slate-500 focus:outline-none focus:border-sky-500 transition"
                  />
                  {externalUrlInput && (
                    <button
                      type="button"
                      onClick={() => {
                        setExternalUrlInput('');
                        setResolvedMediaInfo(null);
                        lastInspectedUrlRef.current = '';
                      }}
                      className="absolute right-2.5 p-1.5 rounded-lg text-slate-400 hover:text-white hover:bg-slate-800 transition cursor-pointer"
                      title="مسح الرابط"
                    >
                      <X className="w-4 h-4" />
                    </button>
                  )}
                </div>

                <button
                  type="button"
                  onClick={handlePasteFromClipboard}
                  className="min-h-[46px] px-4 py-2.5 rounded-xl bg-slate-900 hover:bg-slate-800 border border-slate-700/80 text-slate-200 text-xs font-semibold flex items-center justify-center gap-2 transition cursor-pointer shrink-0 whitespace-nowrap"
                >
                  <ClipboardPaste className="w-4 h-4 text-sky-400 shrink-0" />
                  <span>لصق الرابط وفحصه</span>
                </button>
              </div>
            </div>

            {/* STEP 2: DIRECT INLINE FORMAT, RESOLUTION & FILE SIZE SELECTOR (Immediately after pasting URL) */}
            <div className="p-4 sm:p-5 rounded-2xl bg-slate-950/80 border border-slate-800/90 space-y-4">
              {/* Top Row: Format Switcher (Video MP4 vs Audio MP3) + Inspected Media Title */}
              <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-3">
                <div className="space-y-0.5 min-w-0">
                  <span className="text-xs font-bold text-white block">
                    2. اختر صيغة التحميل والدقة والحجم المناسب
                  </span>
                  {resolvedMediaInfo ? (
                    <p className="text-xs text-emerald-400 font-medium truncate">
                      {resolvedMediaInfo.platformName}
                      {resolvedMediaInfo.durationSec > 0
                        ? ` · ${Math.floor(resolvedMediaInfo.durationSec / 60)}:${String(
                            resolvedMediaInfo.durationSec % 60
                          ).padStart(2, '0')} دقيقة`
                        : ''}{' '}
                      · <span className="text-slate-200">{resolvedMediaInfo.title}</span>
                    </p>
                  ) : (
                    <p className="text-[11px] text-slate-400">
                      حدّد صيغة الفيديو (MP4) أو الصوت (MP3) والدقة المطلوبة — تظهر الأحجام الدقيقة فور لصق الرابط
                    </p>
                  )}
                </div>

                {/* Format Segmented Toggle: MP4 Video | MP3 Audio */}
                <div className="grid grid-cols-2 gap-1.5 p-1 rounded-xl bg-slate-900 border border-slate-800 shrink-0">
                  <button
                    type="button"
                    onClick={() => {
                      setExternalMediaFormat('video');
                      if (!['1080', '720', '480', '360', '240'].includes(externalQuality)) {
                        setExternalQuality('720');
                      }
                    }}
                    className={`min-h-[38px] px-3.5 py-1.5 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                      externalMediaFormat === 'video'
                        ? 'bg-sky-600 text-white shadow-sm'
                        : 'text-slate-400 hover:text-slate-200'
                    }`}
                  >
                    <Film className="w-3.5 h-3.5 shrink-0" />
                    <span>فيديو (MP4)</span>
                  </button>
                  <button
                    type="button"
                    onClick={() => {
                      setExternalMediaFormat('audio');
                      if (!['320', '192', '128'].includes(externalQuality)) {
                        setExternalQuality('320');
                      }
                    }}
                    className={`min-h-[38px] px-3.5 py-1.5 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                      externalMediaFormat === 'audio'
                        ? 'bg-indigo-600 text-white shadow-sm'
                        : 'text-slate-400 hover:text-slate-200'
                    }`}
                  >
                    <Music className="w-3.5 h-3.5 shrink-0" />
                    <span>صوت فقط (MP3)</span>
                  </button>
                </div>
              </div>

              {/* Resolution & Exact Size Grid */}
              {resolvedMediaInfo && resolvedMediaInfo.availableFormats.length > 0 ? (
                <div className="space-y-2.5">
                  <div className="grid grid-cols-1 sm:grid-cols-2 gap-2">
                    {resolvedMediaInfo.availableFormats
                      .filter((fmt) =>
                        resolvedMediaInfo.isVideoPlatform ? fmt.format === externalMediaFormat : true
                      )
                      .map((fmt) => {
                        const isChosen =
                          externalMediaFormat === fmt.format &&
                          (externalQuality === fmt.quality || fmt.quality === 'original');
                        const displayBytes = getEffectiveFormatBytes(fmt, externalCompressMode);
                        const baseOriginal = resolvedMediaInfo.originalSizeBytes || fmt.sizeBytes;
                        const dynamicSavedPct =
                          baseOriginal > 0 && displayBytes > 0 && displayBytes < baseOriginal
                            ? Math.round(((baseOriginal - displayBytes) / baseOriginal) * 100)
                            : fmt.savedPercent;
                        const cleanBadge = fmt.badge.replace(/\s*\([^)]*توفير[^)]*\)/g, '').trim();

                        return (
                          <div
                            key={fmt.id}
                            onClick={() => {
                              setExternalMediaFormat(fmt.format);
                              if (fmt.quality !== 'original') {
                                setExternalQuality(fmt.quality);
                              }
                            }}
                            className={`p-3 rounded-xl border transition cursor-pointer flex items-center justify-between gap-2.5 ${
                              isChosen
                                ? 'bg-sky-500/15 border-sky-500 text-white shadow-sm'
                                : 'bg-slate-900/70 border-slate-800/90 hover:border-slate-700 text-slate-200'
                            }`}
                          >
                            <div className="min-w-0 flex-1 space-y-0.5">
                              <div className="flex items-center gap-1.5 flex-wrap">
                                <span className="text-xs sm:text-sm font-bold text-white">
                                  {fmt.label}
                                </span>
                                {isChosen && (
                                  <span className="text-[11px] font-semibold text-sky-400">
                                    ✓ محدد
                                  </span>
                                )}
                              </div>
                              <div className="flex items-center gap-1.5 text-[11px] text-slate-400 tabular-nums flex-wrap">
                                <span>{cleanBadge}</span>
                                {dynamicSavedPct > 0 && (
                                  <>
                                    <span aria-hidden="true">·</span>
                                    <span className="text-emerald-400 font-semibold">
                                      توفير {dynamicSavedPct}%
                                    </span>
                                  </>
                                )}
                              </div>
                            </div>

                            {/* Right Side: Exact File Size + 1-Tap Quick Download */}
                            <div className="flex items-center gap-2 shrink-0">
                              <div className="text-left">
                                <span
                                  className={`block text-xs sm:text-sm font-bold font-mono tabular-nums ${
                                    isChosen ? 'text-sky-300' : 'text-white'
                                  }`}
                                  dir="ltr"
                                >
                                  {displayBytes > 0 ? formatBytes(displayBytes) : 'تلقائي'}
                                </span>
                                {externalCompressMode === 'zip' && (
                                  <span className="block text-[10px] text-indigo-300 font-medium">
                                    مضغوط ZIP
                                  </span>
                                )}
                                {externalCompressMode === 'media' && (
                                  <span className="block text-[10px] text-emerald-400 font-medium">
                                    مقلّص الحجم
                                  </span>
                                )}
                              </div>

                              <button
                                type="button"
                                onClick={(e) => {
                                  e.stopPropagation();
                                  setExternalMediaFormat(fmt.format);
                                  if (fmt.quality !== 'original') {
                                    setExternalQuality(fmt.quality);
                                  }
                                  const dlParams = buildFormatDownloadParams(
                                    fmt,
                                    externalCompressMode,
                                    externalCustomName,
                                    resolvedMediaInfo.originalSizeBytes || fmt.sizeBytes
                                  );
                                  void startInAppStreamDownload(dlParams);
                                }}
                                className="min-h-[38px] min-w-[38px] px-2.5 py-1.5 rounded-lg bg-sky-600 hover:bg-sky-500 text-white text-xs font-semibold flex items-center justify-center gap-1 transition cursor-pointer shrink-0"
                                title="تحميل مباشر بهذه الصيغة والحجم المحدد"
                              >
                                <Download className="w-3.5 h-3.5" />
                              </button>
                            </div>
                          </div>
                        );
                      })}
                  </div>
                </div>
              ) : (
                /* Pre-Inspection Direct Resolution Picker (Visible before or while link is being inspected) */
                <div className="grid grid-cols-2 sm:grid-cols-5 gap-2">
                  {(externalMediaFormat === 'video' ? videoQualityPresets : audioQualityPresets).map(
                    (preset) => {
                      const active = externalQuality === preset.q;
                      return (
                        <button
                          key={preset.q}
                          type="button"
                          onClick={() => setExternalQuality(preset.q)}
                          className={`min-h-[54px] p-2.5 rounded-xl border text-right transition cursor-pointer flex flex-col justify-between ${
                            active
                              ? 'bg-sky-500/15 border-sky-500 text-white'
                              : 'bg-slate-900/70 border-slate-800/90 hover:border-slate-700 text-slate-300'
                          }`}
                        >
                          <div className="flex items-center justify-between gap-1 w-full">
                            <span className="text-xs font-bold text-white">{preset.title}</span>
                            {active && <Check className="w-3.5 h-3.5 text-sky-400 shrink-0" />}
                          </div>
                          <span className="text-[10px] text-slate-400 mt-1">{preset.desc}</span>
                        </button>
                      );
                    }
                  )}
                </div>
              )}

              {/* Compression Mode (Only shown when Lossless ZIP saves >= 10% without quality loss) & Custom Filename Row */}
              <div className="grid grid-cols-1 sm:grid-cols-2 gap-3 pt-2 border-t border-slate-800/80">
                {resolvedMediaInfo &&
                !resolvedMediaInfo.isVideoPlatform &&
                resolvedMediaInfo.zipEligible &&
                (resolvedMediaInfo.zipSavedPercent || 0) >= 10 ? (
                  <div className="space-y-1.5">
                    <label className="block text-[11px] font-semibold text-emerald-300">
                      ضغط ZIP بدون فقدان الجودة أو الدقة (توفير ~{resolvedMediaInfo.zipSavedPercent}%)
                    </label>
                    <div className="grid grid-cols-2 gap-1.5 p-1 rounded-xl bg-slate-900 border border-slate-800">
                      <button
                        type="button"
                        onClick={() => setExternalCompressMode('none')}
                        className={`min-h-[38px] px-2.5 py-1 rounded-lg text-[11px] font-semibold transition cursor-pointer whitespace-nowrap ${
                          externalCompressMode === 'none'
                            ? 'bg-slate-800 text-white shadow-sm'
                            : 'text-slate-400 hover:text-slate-200'
                        }`}
                      >
                        الحجم الأصلي (بدون ضغط)
                      </button>
                      <button
                        type="button"
                        onClick={() => setExternalCompressMode('zip')}
                        className={`min-h-[38px] px-2.5 py-1 rounded-lg text-[11px] font-semibold transition cursor-pointer whitespace-nowrap ${
                          externalCompressMode === 'zip'
                            ? 'bg-indigo-600 text-white shadow-sm'
                            : 'text-slate-400 hover:text-slate-200'
                        }`}
                      >
                        ضغط ZIP (توفير {resolvedMediaInfo.zipSavedPercent}%)
                      </button>
                    </div>
                  </div>
                ) : (
                  <div className="space-y-1.5">
                    <label className="block text-[11px] font-semibold text-slate-300">
                      طريقة التحميل والحفاظ على الدقة
                    </label>
                    <div className="min-h-[44px] px-3.5 py-2 rounded-xl bg-slate-900/70 border border-slate-800/90 flex items-center justify-between gap-2 text-xs text-slate-300">
                      <span className="truncate">
                        {!resolvedMediaInfo || resolvedMediaInfo.isVideoPlatform
                          ? 'تحميل مباشر بصيغة الحجم المختارة بدون ضغط إضافي'
                          : 'تحميل مباشر بالحجم الأصلي (توفير ZIP أقل من 10%)'}
                      </span>
                      <span className="text-[11px] text-emerald-400 font-semibold shrink-0">
                        بدون فقدان الجودة
                      </span>
                    </div>
                  </div>
                )}

                <div className="space-y-1.5">
                  <label className="block text-[11px] font-semibold text-slate-300">
                    اسم مخصص للملف (اختياري)
                  </label>
                  <input
                    type="text"
                    value={externalCustomName}
                    onChange={(e) => setExternalCustomName(e.target.value)}
                    placeholder="اتركه فارغاً لاستخدام عنوان الفيديو أو الملف الأصلي"
                    className="w-full min-h-[44px] px-3.5 py-2 rounded-xl bg-slate-900 border border-slate-800 text-xs text-white placeholder-slate-500 focus:outline-none focus:border-sky-500"
                  />
                </div>
              </div>

              {/* Live Size Summary Strip when URL is resolved */}
              {resolvedMediaInfo && selectedEffectiveBytes > 0 && (
                <div className="pt-2 border-t border-slate-800/80 flex flex-wrap items-center justify-between gap-2 text-xs text-slate-300 tabular-nums">
                  <div className="flex flex-wrap items-center gap-2">
                    <span>
                      الحجم الأصلي الكامل:{' '}
                      <strong className="text-slate-200 font-mono" dir="ltr">
                        {formatBytes(selectedOriginalBytes)}
                      </strong>
                    </span>
                    <span aria-hidden="true">·</span>
                    <span>
                      حجم اختيارك الحالي:{' '}
                      <strong className="text-emerald-400 font-mono" dir="ltr">
                        {formatBytes(selectedEffectiveBytes)}
                      </strong>
                    </span>
                  </div>
                  {selectedSavedBytes > 0 && (
                    <span className="text-emerald-400 font-semibold">
                      توفير مسبق: {formatBytes(selectedSavedBytes)} ({selectedSavedPercent}%)
                    </span>
                  )}
                </div>
              )}
            </div>

            {/* STEP 3: Destination Selection & Primary Submit Button */}
            <div className="space-y-3">
              <div className="grid grid-cols-3 gap-2 p-1.5 rounded-xl bg-slate-950 border border-slate-800/90">
                <button
                  type="button"
                  onClick={() => setExternalDestination('device')}
                  className={`min-h-[42px] py-2 px-2 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                    externalDestination === 'device'
                      ? 'bg-sky-600 text-white shadow-sm'
                      : 'text-slate-400 hover:text-slate-200'
                  }`}
                >
                  <Download className="w-3.5 h-3.5 shrink-0" />
                  <span>تحميل لجهازي</span>
                </button>
                <button
                  type="button"
                  onClick={() => setExternalDestination('telegram')}
                  className={`min-h-[42px] py-2 px-2 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                    externalDestination === 'telegram'
                      ? 'bg-indigo-600 text-white shadow-sm'
                      : 'text-slate-400 hover:text-slate-200'
                  }`}
                >
                  <Smartphone className="w-3.5 h-3.5 shrink-0" />
                  <span>إلى تليجرام</span>
                </button>
                <button
                  type="button"
                  onClick={() => setExternalDestination('drive')}
                  className={`min-h-[42px] py-2 px-2 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                    externalDestination === 'drive'
                      ? 'bg-emerald-600 text-white shadow-sm'
                      : 'text-slate-400 hover:text-slate-200'
                  }`}
                >
                  <HardDrive className="w-3.5 h-3.5 shrink-0" />
                  <span>إلى Drive</span>
                </button>
              </div>

              <button
                type="submit"
                disabled={submittingUrl || !externalUrlInput.trim()}
                className="w-full min-h-[48px] px-6 py-3 rounded-xl bg-sky-600 hover:bg-sky-500 text-white font-bold text-sm transition flex items-center justify-center gap-2 cursor-pointer disabled:opacity-50 shadow-md"
              >
                {submittingUrl ? (
                  <Loader2 className="w-4 h-4 animate-spin" />
                ) : externalDestination === 'device' ? (
                  <Download className="w-4 h-4" />
                ) : externalDestination === 'telegram' ? (
                  <Send className="w-4 h-4" />
                ) : (
                  <UploadCloud className="w-4 h-4" />
                )}
                <span>
                  {externalDestination === 'device'
                    ? `تحميل لجهازي الآن (${
                        externalMediaFormat === 'audio' ? `MP3 • ${externalQuality}kbps` : `MP4 • ${externalQuality}p`
                      }${selectedEffectiveBytes > 0 ? ` — ${formatBytes(selectedEffectiveBytes)}` : ''})`
                    : externalDestination === 'telegram'
                      ? `إرسال لتليجرام (${
                          externalMediaFormat === 'audio' ? `MP3 • ${externalQuality}kbps` : `MP4 • ${externalQuality}p`
                        }${selectedEffectiveBytes > 0 ? ` — ${formatBytes(selectedEffectiveBytes)}` : ''})`
                      : `رفع إلى Google Drive (${
                          externalMediaFormat === 'audio' ? `MP3 • ${externalQuality}kbps` : `MP4 • ${externalQuality}p`
                        }${selectedEffectiveBytes > 0 ? ` — ${formatBytes(selectedEffectiveBytes)}` : ''})`}
                </span>
              </button>
            </div>
          </form>

          {/* In-App Live Download Progress Bar with Pause / Resume / Cancel */}
          {inAppDownload && (
            <div className="p-4 rounded-2xl bg-slate-950/90 border border-sky-500/40 space-y-3">
              <div className="flex flex-wrap items-center justify-between gap-2">
                <div className="flex items-center gap-2.5 min-w-0">
                  <div
                    className={`w-9 h-9 rounded-xl flex items-center justify-center shrink-0 border ${
                      inAppDownload.status === 'completed'
                        ? 'bg-emerald-500/20 border-emerald-500/40 text-emerald-400'
                        : inAppDownload.status === 'paused'
                          ? 'bg-amber-500/20 border-amber-500/40 text-amber-400'
                          : inAppDownload.status === 'cancelled' || inAppDownload.status === 'failed'
                            ? 'bg-rose-500/20 border-rose-500/40 text-rose-400'
                            : 'bg-sky-500/20 border-sky-500/40 text-sky-400'
                    }`}
                  >
                    {inAppDownload.status === 'downloading' ||
                    inAppDownload.status === 'worker_processing' ? (
                      <Loader2 className="w-5 h-5 animate-spin" />
                    ) : inAppDownload.status === 'completed' ? (
                      <CheckCircle2 className="w-5 h-5" />
                    ) : inAppDownload.status === 'paused' ? (
                      <Pause className="w-5 h-5" />
                    ) : (
                      <AlertTriangle className="w-5 h-5" />
                    )}
                  </div>
                  <div className="min-w-0">
                    <div className="flex items-center gap-2 flex-wrap text-xs text-slate-300">
                      <span className="font-bold text-sky-300">
                        {inAppDownload.status === 'worker_processing'
                          ? inAppDownload.workerStageLabel || 'عامل ضغط الفيديو المستقل: جاري تقليص الحجم...'
                          : inAppDownload.status === 'downloading'
                            ? 'جاري التحميل المباشر داخل التطبيق...'
                            : inAppDownload.status === 'paused'
                              ? 'التحميل متوقف مؤقتاً'
                              : inAppDownload.status === 'completed'
                                ? 'اكتمل التحميل بنجاح (100%)'
                                : inAppDownload.status === 'cancelled'
                                  ? 'تم إلغاء التحميل'
                                  : 'فشل التحميل'}
                      </span>
                      <span aria-hidden="true">·</span>
                      <span>{inAppDownload.formatLabel}</span>
                    </div>
                    <p className="text-sm font-bold text-white truncate mt-0.5" dir="ltr">
                      {inAppDownload.fileName}
                    </p>
                  </div>
                </div>

                {/* Pause/Resume & Cancel Controls */}
                <div className="flex items-center gap-2 shrink-0">
                  {(inAppDownload.status === 'downloading' ||
                    inAppDownload.status === 'worker_processing' ||
                    inAppDownload.status === 'paused') && (
                    <>
                      {inAppDownload.status !== 'worker_processing' && (
                        <button
                          type="button"
                          onClick={togglePauseInAppDownload}
                          className={`min-h-[38px] px-3 py-1.5 rounded-xl text-xs font-bold flex items-center gap-1.5 transition cursor-pointer ${
                            inAppDownload.status === 'paused'
                              ? 'bg-emerald-600 hover:bg-emerald-500 text-white'
                              : 'bg-amber-500/20 hover:bg-amber-500/30 border border-amber-500/40 text-amber-200'
                          }`}
                        >
                          {inAppDownload.status === 'paused' ? (
                            <>
                              <Play className="w-3.5 h-3.5" />
                              <span>استئناف</span>
                            </>
                          ) : (
                            <>
                              <Pause className="w-3.5 h-3.5" />
                              <span>إيقاف مؤقت</span>
                            </>
                          )}
                        </button>
                      )}

                      <button
                        type="button"
                        onClick={cancelInAppDownload}
                        className="min-h-[38px] px-3 py-1.5 rounded-xl bg-rose-500/20 hover:bg-rose-500/30 border border-rose-500/40 text-rose-200 text-xs font-bold flex items-center gap-1.5 transition cursor-pointer"
                      >
                        <Ban className="w-3.5 h-3.5" />
                        <span>إلغاء</span>
                      </button>
                    </>
                  )}

                  {inAppDownload.status === 'completed' && inAppDownload.blobUrl && (
                    <button
                      type="button"
                      onClick={() => triggerBrowserBlobSave(inAppDownload.blobUrl!, inAppDownload.fileName)}
                      className="min-h-[38px] px-3 py-1.5 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white text-xs font-bold flex items-center gap-1.5 transition cursor-pointer"
                    >
                      <Download className="w-3.5 h-3.5" />
                      <span>حفظ الملف للجهاز</span>
                    </button>
                  )}

                  {(inAppDownload.status === 'completed' ||
                    inAppDownload.status === 'cancelled' ||
                    inAppDownload.status === 'failed') && (
                    <button
                      type="button"
                      onClick={() => setInAppDownload(null)}
                      className="min-h-[38px] min-w-[38px] p-1.5 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-400 hover:text-white flex items-center justify-center transition cursor-pointer"
                      title="إغلاق شريط التحميل"
                    >
                      <X className="w-4 h-4" />
                    </button>
                  )}
                </div>
              </div>

              {/* Progress Bar Track */}
              <div className="w-full h-2.5 bg-slate-900 rounded-full overflow-hidden border border-slate-800">
                <div
                  className={`h-full transition-all duration-200 ${
                    inAppDownload.status === 'completed'
                      ? 'bg-emerald-500'
                      : inAppDownload.status === 'paused'
                        ? 'bg-amber-500'
                        : inAppDownload.status === 'cancelled' || inAppDownload.status === 'failed'
                          ? 'bg-rose-500'
                          : 'bg-sky-500'
                  }`}
                  style={{ width: `${Math.max(inAppDownload.status === 'downloading' ? 3 : 0, inAppDownload.percent)}%` }}
                />
              </div>

              {/* Live Metrics Footer */}
              <div className="flex flex-wrap items-center justify-between gap-2 text-xs text-slate-300 tabular-nums">
                <div className="flex items-center gap-2 flex-wrap">
                  <span className="font-bold text-white" dir="ltr">
                    {inAppDownload.percent}%
                  </span>
                  <span aria-hidden="true">·</span>
                  <span dir="ltr">
                    {formatBytes(inAppDownload.bytesLoaded)}
                    {inAppDownload.totalBytes > 0 ? ` / ${formatBytes(inAppDownload.totalBytes)}` : ''}
                  </span>
                  {inAppDownload.status === 'downloading' && inAppDownload.speedBps > 0 && (
                    <>
                      <span aria-hidden="true">·</span>
                      <span className="text-emerald-400 font-bold" dir="ltr">
                        {formatBytes(inAppDownload.speedBps)}/s
                      </span>
                    </>
                  )}
                </div>

                {inAppDownload.originalBytes > 0 &&
                  inAppDownload.totalBytes > 0 &&
                  inAppDownload.originalBytes > inAppDownload.totalBytes && (
                    <div className="text-[11px] text-emerald-300 font-semibold flex items-center gap-1.5">
                      <span>الأصلي: {formatBytes(inAppDownload.originalBytes)}</span>
                      <span>←</span>
                      <span>الحجم الفعلي: {formatBytes(inAppDownload.totalBytes)}</span>
                    </div>
                  )}
              </div>

              {inAppDownload.errorMessage && (
                <p className="text-xs text-rose-300 bg-rose-950/50 border border-rose-500/30 rounded-lg p-2">
                  {inAppDownload.errorMessage}
                </p>
              )}
            </div>
          )}
        </section>

        {/* Core Card 2: Live Personal Transfer Queue & History */}
        <section className="w-full bg-[#0F1626] border border-slate-800/90 rounded-2xl p-4 sm:p-6 space-y-4">
          <div className="flex flex-wrap items-center justify-between gap-3 border-b border-slate-800/80 pb-3.5">
            <div className="flex items-center gap-2">
              <Activity className="w-4 h-4 text-sky-400" />
              <h2 className="text-base font-bold text-white">العمليات الجارية وسجل النقل</h2>
            </div>

            <div className="flex items-center gap-2">
              {(serverStatus?.stats.activeJobs || 0) + (serverStatus?.stats.waitingAuthJobs || 0) > 0 && (
                <button
                  onClick={() => handleCancelAllJobs('personal')}
                  className="min-h-[38px] px-3 py-1.5 rounded-lg bg-rose-500/10 hover:bg-rose-500/20 border border-rose-500/30 text-rose-300 text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer"
                >
                  <Ban className="w-3.5 h-3.5" />
                  <span>إلغاء الجارية</span>
                </button>
              )}

              {(serverStatus?.stats.failedJobs || 0) > 0 && (
                <button
                  onClick={handleClearFailedJobs}
                  disabled={clearingFailed}
                  className="min-h-[38px] px-3 py-1.5 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-300 text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer"
                >
                  <Trash2 className="w-3.5 h-3.5 text-rose-400" />
                  <span>مسح الفاشلة ({serverStatus?.stats.failedJobs})</span>
                </button>
              )}
            </div>
          </div>

          {!serverStatus || serverStatus.jobs.length === 0 ? (
            <div className="py-10 px-4 text-center border border-dashed border-slate-800 rounded-xl space-y-1.5">
              <p className="text-sm text-slate-300 font-medium">لا توجد عمليات نقل حالياً</p>
              <p className="text-xs text-slate-500">
                ضع أي رابط في الأعلى أو أرسل ملفاً لبوت تليجرام لتظهر حالة النقل والسرعة هنا.
              </p>
            </div>
          ) : (
            <div className="space-y-2.5 max-h-[500px] overflow-y-auto pr-1">
              {serverStatus.jobs.map((job) => {
                const pct =
                  job.totalBytes > 0
                    ? Math.min(100, Math.round((job.bytesTransferred / job.totalBytes) * 100))
                    : job.status === 'completed'
                    ? 100
                    : 0;
                const isActive =
                  job.status === 'downloading' ||
                  job.status === 'uploading' ||
                  job.status === 'queued' ||
                  job.status === 'waiting_auth';

                return (
                  <div
                    key={job.id}
                    className="p-3.5 rounded-xl bg-slate-900/75 border border-slate-800/90 space-y-2"
                  >
                    <div className="flex flex-wrap items-center justify-between gap-2">
                      <div className="flex items-center gap-2 min-w-0">
                        <FileText className="w-4 h-4 text-sky-400 shrink-0" />
                        <span className="font-semibold text-sm text-white truncate max-w-[180px] sm:max-w-md" dir="auto">
                          {job.fileName}
                        </span>
                        <span className="text-xs text-slate-400 shrink-0">
                          ·{' '}
                          {job.direction === 'to_telegram'
                            ? 'إلى تليجرام'
                            : job.direction === 'to_device'
                            ? 'لجهازي'
                            : 'إلى Drive'}
                        </span>
                      </div>

                      <div className="flex items-center gap-2">
                        {job.status === 'completed' && (
                          <span className="text-xs text-emerald-400 font-semibold">
                            {job.isDuplicateSkipped ? 'موجود مسبقاً' : 'مكتمل'}
                          </span>
                        )}
                        {(job.status === 'uploading' || job.status === 'downloading') && (
                          <span className="text-xs text-sky-300 font-semibold flex items-center gap-1 tabular-nums">
                            <Loader2 className="w-3 h-3 animate-spin" />
                            {pct}%
                          </span>
                        )}
                        {job.status === 'waiting_auth' && (
                          <span className="text-xs text-amber-300">بانتظار ربط Drive</span>
                        )}
                        {job.status === 'cancelled' && (
                          <span className="text-xs text-slate-400">ملغى</span>
                        )}
                        {job.status === 'failed' && (
                          <span className="text-xs text-rose-400">فشل</span>
                        )}

                        {isActive && (
                          <button
                            onClick={() => handleCancelJob(job.id)}
                            className="px-2.5 py-1 rounded-lg bg-rose-500/15 hover:bg-rose-500/25 text-rose-300 text-xs font-semibold transition cursor-pointer"
                          >
                            إلغاء
                          </button>
                        )}

                        {(job.status === 'failed' || job.status === 'cancelled') && (
                          <>
                            <button
                              onClick={() => handleRetryJob(job.id)}
                              className="px-2.5 py-1 rounded-lg bg-sky-500/15 hover:bg-sky-500/25 text-sky-300 text-xs font-semibold transition cursor-pointer"
                            >
                              إعادة
                            </button>
                            <button
                              onClick={() => handleDeleteJob(job.id)}
                              className="p-1 rounded-lg bg-slate-800 hover:bg-rose-950/60 text-slate-400 hover:text-rose-300 transition cursor-pointer"
                            >
                              <Trash2 className="w-3.5 h-3.5" />
                            </button>
                          </>
                        )}
                      </div>
                    </div>

                    {(job.status === 'uploading' || job.status === 'downloading') && (
                      <div className="w-full h-1.5 bg-slate-800 rounded-full overflow-hidden">
                        <div
                          className="h-full bg-sky-500 transition-all duration-200"
                          style={{ width: `${Math.max(4, pct)}%` }}
                        />
                      </div>
                    )}

                    <div className="flex flex-wrap items-center justify-between gap-2 text-xs text-slate-400">
                      <div className="flex flex-wrap items-center gap-2 tabular-nums">
                        <span dir="ltr">
                          {formatBytes(job.bytesTransferred || job.totalBytes)}
                          {job.totalBytes > 0 &&
                          job.bytesTransferred > 0 &&
                          job.bytesTransferred < job.totalBytes
                            ? ` / ${formatBytes(job.totalBytes)}`
                            : ''}
                        </span>
                        {job.speedBps && job.speedBps > 0 && (
                          <>
                            <span aria-hidden="true">·</span>
                            <span className="text-emerald-400 font-semibold" dir="ltr">
                              {formatBytes(job.speedBps)}/s
                            </span>
                          </>
                        )}
                        {job.folderName && (
                          <>
                            <span aria-hidden="true">·</span>
                            <span>{job.folderName}</span>
                          </>
                        )}
                      </div>

                      <div className="flex items-center gap-3">
                        {(job.driveFileId || job.directUrl) && (
                          <button
                            type="button"
                            disabled={downloadingItemId === job.id}
                            onClick={() =>
                              handleAuthenticatedProxyDownload(
                                `/api/direct-download/${encodeURIComponent(job.fileName)}?jobId=${encodeURIComponent(
                                  job.id
                                )}${job.directUrl ? `&url=${encodeURIComponent(job.directUrl)}` : ''}${
                                  job.driveFileId ? `&driveFileId=${encodeURIComponent(job.driveFileId)}` : ''
                                }${job.compressMode ? `&compress=${encodeURIComponent(job.compressMode)}` : ''}${
                                  personalEmail ? `&userEmail=${encodeURIComponent(personalEmail)}` : ''
                                }${personalChatId ? `&chatId=${encodeURIComponent(personalChatId)}` : ''}`,
                                job.fileName,
                                job.id
                              )
                            }
                            className="text-indigo-400 hover:text-indigo-300 font-semibold flex items-center gap-1 cursor-pointer disabled:opacity-50"
                          >
                            {downloadingItemId === job.id ? (
                              <Loader2 className="w-3.5 h-3.5 animate-spin" />
                            ) : (
                              <Download className="w-3.5 h-3.5" />
                            )}
                            <span>تحميل</span>
                          </button>
                        )}
                        {job.webViewLink && (
                          <a
                            href={job.webViewLink}
                            target="_blank"
                            rel="noreferrer"
                            className="text-sky-400 hover:text-sky-300 font-semibold flex items-center gap-1"
                          >
                            <span>فتح في Drive</span>
                            <ExternalLink className="w-3.5 h-3.5" />
                          </a>
                        )}
                      </div>
                    </div>

                    {job.errorMessage && (
                      <p className="text-xs text-rose-400 bg-rose-950/30 border border-rose-500/20 rounded-lg px-3 py-1.5 break-words">
                        {job.errorMessage}
                      </p>
                    )}
                  </div>
                );
              })}
            </div>
          )}
        </section>
      </main>

      {/* =====================================================================
          POPUP MENU & POPUP PAGES (القائمة المنبثقة وكل خيار تنبثق منه صفحته)
         ===================================================================== */}
      {activeModal && (
        <div
          className="fixed inset-0 z-50 bg-black/75 backdrop-blur-sm flex items-center justify-center p-3 sm:p-6 overflow-y-auto"
          onClick={() => setActiveModal(null)}
        >
          <div
            className={`bg-[#0D1322] border border-slate-800 rounded-2xl w-full ${
              activeModal === 'menu' || activeModal === 'pwa_install' ? 'max-w-md' : 'max-w-2xl'
            } max-h-[88vh] flex flex-col shadow-2xl overflow-hidden`}
            onClick={(e) => e.stopPropagation()}
          >
            {/* Modal Header with Back-to-Menu & Close */}
            <div className="px-4 sm:px-5 py-3.5 border-b border-slate-800 flex items-center justify-between gap-2 shrink-0">
              <div className="flex items-center gap-2 min-w-0">
                {activeModal !== 'menu' && (
                  <button
                    type="button"
                    onClick={() => setActiveModal('menu')}
                    className="px-2.5 py-1 rounded-lg bg-slate-900 hover:bg-slate-800 border border-slate-700 text-slate-300 text-xs font-medium flex items-center gap-1 cursor-pointer shrink-0"
                  >
                    <ArrowRight className="w-3.5 h-3.5" />
                    <span>القائمة</span>
                  </button>
                )}
                <h2 className="text-sm sm:text-base font-bold text-white truncate">
                  {activeModal === 'menu' && 'قائمة الخيارات والبوابات المنبثقة'}
                  {activeModal === 'pwa_install' && 'تثبيت التطبيق على شاشة الهاتف'}
                  {activeModal === 'drive_files' && 'ملفاتي ومجلداتي في Google Drive'}
                  {activeModal === 'large_upload' && 'رفع الملفات الضخمة مباشرة'}
                  {activeModal === 'settings' && 'حسابي الشخصي وإعدادات الربط'}
                  {activeModal === 'admin' && 'إدارة البوت وتشغيل Vercel'}
                  {activeModal === 'url_options' && 'خيارات الجودة والضغط للسحب'}
                </h2>
              </div>

              <button
                onClick={() => setActiveModal(null)}
                className="p-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 text-slate-400 hover:text-white transition cursor-pointer shrink-0"
                aria-label="إغلاق النافذة"
              >
                <X className="w-4 h-4" />
              </button>
            </div>

            {/* Modal Body */}
            <div className="p-4 sm:p-5 overflow-y-auto space-y-4 flex-1">
              {/* POPUP 0: THE TOP MENU LAUNCHER */}
              {activeModal === 'menu' && (
                <div className="space-y-2.5">
                  <p className="text-xs text-slate-400 mb-3">
                    اختر أي قسم لفتح صفحته المنبثقة الخاصة:
                  </p>

                  {/* Option 0: Install App on Phone Home Screen */}
                  {!isInstalled && (
                    <button
                      type="button"
                      onClick={handleInstallButtonClick}
                      className="w-full p-3.5 rounded-xl bg-emerald-950/40 hover:bg-emerald-950/60 border border-emerald-500/40 flex items-center justify-between gap-3 text-right transition cursor-pointer"
                    >
                      <div className="flex items-center gap-3 min-w-0">
                        <div className="w-10 h-10 rounded-xl bg-emerald-500/20 border border-emerald-500/40 flex items-center justify-center text-emerald-400 shrink-0">
                          <Smartphone className="w-5 h-5" />
                        </div>
                        <div className="min-w-0">
                          <p className="text-sm font-bold text-white">تثبيت التطبيق على شاشة الهاتف</p>
                          <p className="text-xs text-emerald-300/90 truncate mt-0.5">
                            إضافة أيقونة TeleDrive على الشاشة الرئيسية للفتح السريع كتطبيق مستقل
                          </p>
                        </div>
                      </div>
                      <ChevronLeft className="w-4 h-4 text-emerald-400 shrink-0" />
                    </button>
                  )}

                  {/* Option 1: Personal Account & Link Settings */}
                  <button
                    type="button"
                    onClick={() => setActiveModal('settings')}
                    className="w-full p-3.5 rounded-xl bg-slate-900/80 hover:bg-slate-800/90 border border-slate-800 flex items-center justify-between gap-3 text-right transition cursor-pointer"
                  >
                    <div className="flex items-center gap-3 min-w-0">
                      <div className="w-10 h-10 rounded-xl bg-emerald-500/15 border border-emerald-500/30 flex items-center justify-center text-emerald-400 shrink-0">
                        <User className="w-5 h-5" />
                      </div>
                      <div className="min-w-0">
                        <p className="text-sm font-bold text-white">حسابي الشخصي وإعدادات الربط</p>
                        <p className="text-xs text-slate-400 truncate mt-0.5">
                          {driveConnected
                            ? `متصل: ${effectiveUserEmail || effectiveUserName}`
                            : 'ربط حساب Google Drive ومحادثة تليجرام والخيارات'}
                        </p>
                      </div>
                    </div>
                    <ChevronLeft className="w-4 h-4 text-slate-500 shrink-0" />
                  </button>

                  {/* Option 2: Drive Files & Folders */}
                  <button
                    type="button"
                    onClick={() => {
                      setActiveModal('drive_files');
                      if (accessToken) refreshDriveFoldersAndFiles();
                    }}
                    className="w-full p-3.5 rounded-xl bg-slate-900/80 hover:bg-slate-800/90 border border-slate-800 flex items-center justify-between gap-3 text-right transition cursor-pointer"
                  >
                    <div className="flex items-center gap-3 min-w-0">
                      <div className="w-10 h-10 rounded-xl bg-sky-500/15 border border-sky-500/30 flex items-center justify-center text-sky-400 shrink-0">
                        <HardDrive className="w-5 h-5" />
                      </div>
                      <div className="min-w-0">
                        <p className="text-sm font-bold text-white">ملفاتي ومجلداتي في Google Drive</p>
                        <p className="text-xs text-slate-400 truncate mt-0.5">
                          اختيار أو إنشاء مجلد الحفظ وتصفح ملفاتك وإرسالها لتليجرام
                        </p>
                      </div>
                    </div>
                    <ChevronLeft className="w-4 h-4 text-slate-500 shrink-0" />
                  </button>

                  {/* Option 3: Large Local File Upload */}
                  <button
                    type="button"
                    onClick={() => setActiveModal('large_upload')}
                    className="w-full p-3.5 rounded-xl bg-slate-900/80 hover:bg-slate-800/90 border border-slate-800 flex items-center justify-between gap-3 text-right transition cursor-pointer"
                  >
                    <div className="flex items-center gap-3 min-w-0">
                      <div className="w-10 h-10 rounded-xl bg-indigo-500/15 border border-indigo-500/30 flex items-center justify-center text-indigo-400 shrink-0">
                        <UploadCloud className="w-5 h-5" />
                      </div>
                      <div className="min-w-0">
                        <p className="text-sm font-bold text-white">رفع الملفات الضخمة مباشرة</p>
                        <p className="text-xs text-slate-400 truncate mt-0.5">
                          رفع مباشر مقسم من جهازك إلى Google Drive لأي حجم (1GB+)
                        </p>
                      </div>
                    </div>
                    <ChevronLeft className="w-4 h-4 text-slate-500 shrink-0" />
                  </button>

                  {/* Option 4: Bot Admin & Vercel Webhook */}
                  <button
                    type="button"
                    onClick={() => setActiveModal('admin')}
                    className="w-full p-3.5 rounded-xl bg-slate-900/80 hover:bg-slate-800/90 border border-slate-800 flex items-center justify-between gap-3 text-right transition cursor-pointer"
                  >
                    <div className="flex items-center gap-3 min-w-0">
                      <div className="w-10 h-10 rounded-xl bg-amber-500/15 border border-amber-500/30 flex items-center justify-center text-amber-400 shrink-0">
                        <ShieldAlert className="w-5 h-5" />
                      </div>
                      <div className="min-w-0">
                        <p className="text-sm font-bold text-white">إدارة البوت وتشغيل Vercel</p>
                        <p className="text-xs text-slate-400 truncate mt-0.5">
                          تفعيل Webhook لـ Vercel، التحكم بالبوت، وإدارة المستخدمين
                        </p>
                      </div>
                    </div>
                    <ChevronLeft className="w-4 h-4 text-slate-500 shrink-0" />
                  </button>
                </div>
              )}

              {/* MODAL: PWA INSTALL ON PHONE HOME SCREEN */}
              {activeModal === 'pwa_install' && (
                <div className="space-y-4">
                  <div className="p-4 rounded-xl bg-slate-900/80 border border-slate-800 flex items-center gap-3.5">
                    <img
                      src="/pwa-192x192.png"
                      alt="TeleDrive App Icon"
                      referrerPolicy="no-referrer"
                      className="w-14 h-14 rounded-2xl border border-slate-700 shrink-0"
                    />
                    <div className="space-y-1">
                      <h3 className="text-sm font-bold text-white">تطبيق TeleDrive Cloud</h3>
                      <p className="text-xs text-slate-400">
                        يعمل كتطبيق مستقل بملء الشاشة على هاتفك لسهولة لصق الروابط والتحميل المباشر.
                      </p>
                    </div>
                  </div>

                  {isInstallable && (
                    <button
                      type="button"
                      onClick={async () => {
                        const ok = await triggerPwaInstall();
                        if (ok) setActiveModal(null);
                      }}
                      className="w-full min-h-[46px] py-2.5 px-4 rounded-xl bg-emerald-600 hover:bg-emerald-500 text-white text-xs font-bold flex items-center justify-center gap-2 transition cursor-pointer shadow-md"
                    >
                      <Download className="w-4 h-4" />
                      <span>تثبيت التطبيق مباشرة الآن</span>
                    </button>
                  )}

                  {!isIOS ? (
                    <div className="p-4 rounded-xl bg-slate-950 border border-slate-800 space-y-2.5 text-xs">
                      <p className="font-bold text-sky-300">
                        طريقة التثبيت على هواتف أندرويد (متصفح Chrome):
                      </p>
                      <ol className="list-decimal list-inside space-y-2 text-slate-300 leading-relaxed">
                        <li>
                          اضغط على زر القائمة <strong className="text-white">(⋮)</strong> في أعلى يسار أو يمين متصفح Chrome.
                        </li>
                        <li>
                          اختر <strong className="text-emerald-300">"تثبيت التطبيق" (Install app)</strong> أو{' '}
                          <strong className="text-emerald-300">"الإضافة إلى الشاشة الرئيسية"</strong>.
                        </li>
                        <li>
                          اضغط <strong className="text-white">تثبيت</strong> لتظهر أيقونة التطبيق مباشرة بين تطبيقات هاتفك.
                        </li>
                      </ol>
                    </div>
                  ) : (
                    <div className="p-4 rounded-xl bg-slate-950 border border-slate-800 space-y-2.5 text-xs">
                      <p className="font-bold text-sky-300">
                        طريقة التثبيت على آيفون وآيباد (متصفح Safari):
                      </p>
                      <ol className="list-decimal list-inside space-y-2 text-slate-300 leading-relaxed">
                        <li className="flex items-center gap-1.5 flex-wrap">
                          <span>1. اضغط على زر المشاركة</span>
                          <Share2 className="w-3.5 h-3.5 text-sky-400 inline" />
                          <strong className="text-white">(Share)</strong>
                          <span>في الشريط السفلي لمتصفح Safari.</span>
                        </li>
                        <li className="flex items-center gap-1.5 flex-wrap">
                          <span>2. مرر للأسفل واختر</span>
                          <PlusSquare className="w-3.5 h-3.5 text-emerald-400 inline" />
                          <strong className="text-emerald-300">"إضافة إلى الشاشة الرئيسية" (Add to Home Screen)</strong>.
                        </li>
                        <li>
                          3. اضغط <strong className="text-white">إضافة (Add)</strong> في أعلى الزاوية ليظهر التطبيق على شاشتك.
                        </li>
                      </ol>
                    </div>
                  )}

                  <div className="pt-1 flex justify-end">
                    <button
                      type="button"
                      onClick={() => setActiveModal(null)}
                      className="min-h-[40px] px-5 py-2 rounded-xl bg-slate-800 hover:bg-slate-700 text-slate-200 text-xs font-semibold cursor-pointer"
                    >
                      حسناً، فهمت
                    </button>
                  </div>
                </div>
              )}

              {/* MODAL 2: DRIVE FILES & FOLDERS */}
              {activeModal === 'drive_files' && (
                <div className="space-y-5">
                  {!accessToken ? (
                    <div className="p-8 text-center space-y-3 bg-slate-900/50 border border-slate-800 rounded-xl">
                      <HardDrive className="w-10 h-10 text-sky-400 mx-auto" />
                      <p className="text-sm font-bold text-white">سجل الدخول بحسابك الشخصي في Google Drive</p>
                      <p className="text-xs text-slate-400 max-w-md mx-auto">
                        لتصفح ملفاتك ومجلداتك أو إرسال أي ملف من Google Drive إلى تليجرام، يرجى ربط حسابك أولاً.
                      </p>
                      <button
                        onClick={handleSignIn}
                        className="px-5 py-2 rounded-xl bg-sky-600 hover:bg-sky-500 text-white font-semibold text-xs transition inline-flex items-center gap-2 cursor-pointer"
                      >
                        <HardDrive className="w-4 h-4" />
                        <span>تسجيل الدخول بـ Google</span>
                      </button>
                    </div>
                  ) : (
                    <>
                      {/* Folder Selector & Creator */}
                      <div className="p-4 rounded-xl bg-slate-900/60 border border-slate-800 space-y-3">
                        <div className="flex flex-wrap items-center justify-between gap-2">
                          <span className="text-xs font-bold text-white flex items-center gap-1.5">
                            <FolderCheck className="w-4 h-4 text-emerald-400" />
                            <span>المجلد النشط للحفظ: {selectedFolderName}</span>
                          </span>

                          <form onSubmit={handleCreateNewFolder} className="flex items-center gap-2 w-full sm:w-auto">
                            <input
                              type="text"
                              value={newFolderInput}
                              onChange={(e) => setNewFolderInput(e.target.value)}
                              placeholder="اسم مجلد جديد..."
                              className="flex-1 px-3 py-1.5 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                            />
                            <button
                              type="submit"
                              disabled={creatingFolder || !newFolderInput.trim()}
                              className="px-3 py-1.5 rounded-lg bg-emerald-600 hover:bg-emerald-500 disabled:opacity-50 text-white font-semibold text-xs flex items-center gap-1 cursor-pointer shrink-0"
                            >
                              {creatingFolder ? <Loader2 className="w-3.5 h-3.5 animate-spin" /> : <FolderPlus className="w-3.5 h-3.5" />}
                              <span>إنشاء</span>
                            </button>
                          </form>
                        </div>

                        {folders.length > 0 && (
                          <div className="grid grid-cols-2 sm:grid-cols-3 gap-2 pt-1 max-h-36 overflow-y-auto">
                            {folders.map((folder) => {
                              const isSelected =
                                folder.id === (selectedFolderId || serverStatus?.drive.activeFolderId);
                              return (
                                <button
                                  key={folder.id}
                                  onClick={() => handleSelectFolder(folder)}
                                  className={`p-2 rounded-lg border text-right transition flex items-center justify-between gap-1.5 cursor-pointer ${
                                    isSelected
                                      ? 'bg-emerald-500/15 border-emerald-500/40 text-emerald-300 font-semibold'
                                      : 'bg-slate-950/60 border-slate-800 text-slate-300 hover:border-slate-700'
                                  }`}
                                >
                                  <span className="text-xs truncate">{folder.name}</span>
                                  {isSelected && <Check className="w-3.5 h-3.5 text-emerald-400 shrink-0" />}
                                </button>
                              );
                            })}
                          </div>
                        )}
                      </div>

                      {/* Files Browser */}
                      <div className="space-y-3">
                        <div className="flex items-center justify-between gap-2">
                          <div className="relative flex-1">
                            <Search className="w-4 h-4 text-slate-500 absolute right-3 top-1/2 -translate-y-1/2" />
                            <input
                              type="text"
                              value={searchQuery}
                              onChange={(e) => setSearchQuery(e.target.value)}
                              placeholder="بحث في ملفات Google Drive..."
                              className="w-full pr-9 pl-3 py-2 bg-slate-950 border border-slate-800 rounded-xl text-xs text-white placeholder-slate-500"
                            />
                          </div>
                          <button
                            onClick={() => refreshDriveFoldersAndFiles()}
                            disabled={filesLoading}
                            className="p-2 rounded-xl bg-slate-900 hover:bg-slate-800 border border-slate-800 text-slate-300 cursor-pointer"
                            title="تحديث القائمة"
                          >
                            <RefreshCw className={`w-4 h-4 ${filesLoading ? 'animate-spin text-sky-400' : ''}`} />
                          </button>
                        </div>

                        {filesLoading ? (
                          <div className="py-8 text-center text-slate-400 flex items-center justify-center gap-2 text-xs">
                            <Loader2 className="w-4 h-4 animate-spin text-sky-400" />
                            <span>جاري تحميل ملفاتك...</span>
                          </div>
                        ) : filteredDriveFiles.length === 0 ? (
                          <div className="py-8 text-center text-slate-500 text-xs">
                            لا توجد ملفات مطابقة.
                          </div>
                        ) : (
                          <div className="divide-y divide-slate-800/60 border border-slate-800 rounded-xl overflow-hidden">
                            {filteredDriveFiles.map((file) => (
                              <div
                                key={file.id}
                                className="p-3 bg-slate-900/40 hover:bg-slate-900/80 flex flex-wrap items-center justify-between gap-2 text-xs"
                              >
                                <div className="min-w-0 flex-1">
                                  <p className="font-medium text-slate-200 truncate" dir="auto">
                                    {file.name}
                                  </p>
                                  <p className="text-[11px] text-slate-500 tabular-nums" dir="ltr">
                                    {formatBytes(file.size)}
                                  </p>
                                </div>

                                <div className="flex items-center gap-1.5 shrink-0">
                                  <button
                                    onClick={() => handleSendDriveFileToTelegram(file)}
                                    disabled={sendingDriveFileId === file.id}
                                    className="px-2.5 py-1 rounded-lg bg-sky-500/15 hover:bg-sky-500/25 text-sky-300 font-semibold flex items-center gap-1 cursor-pointer"
                                  >
                                    {sendingDriveFileId === file.id ? (
                                      <Loader2 className="w-3 h-3 animate-spin" />
                                    ) : (
                                      <Send className="w-3 h-3" />
                                    )}
                                    <span>لتليجرام</span>
                                  </button>

                                  <button
                                    type="button"
                                    disabled={downloadingItemId === file.id}
                                    onClick={() =>
                                      handleAuthenticatedProxyDownload(
                                        `/api/direct-download/${encodeURIComponent(
                                          file.name
                                        )}?driveFileId=${encodeURIComponent(file.id)}${
                                          personalEmail ? `&userEmail=${encodeURIComponent(personalEmail)}` : ''
                                        }${personalChatId ? `&chatId=${encodeURIComponent(personalChatId)}` : ''}`,
                                        file.name,
                                        file.id
                                      )
                                    }
                                    className="px-2.5 py-1 rounded-lg bg-indigo-500/15 hover:bg-indigo-500/25 text-indigo-300 font-semibold flex items-center gap-1 cursor-pointer disabled:opacity-50"
                                  >
                                    {downloadingItemId === file.id ? (
                                      <Loader2 className="w-3 h-3 animate-spin" />
                                    ) : (
                                      <Download className="w-3 h-3" />
                                    )}
                                    <span>تحميل</span>
                                  </button>

                                  {(() => {
                                    const zipCheck = evaluateFileLosslessZipInfo(file.name, file.mimeType);
                                    if (!zipCheck.zipEligible || zipCheck.zipSavedPercent < 10) return null;
                                    const zipItemKey = `${file.id}_zip`;
                                    const zipName = file.name.toLowerCase().endsWith('.zip')
                                      ? file.name
                                      : `${file.name}.zip`;
                                    return (
                                      <button
                                        type="button"
                                        disabled={downloadingItemId === zipItemKey}
                                        onClick={() =>
                                          handleAuthenticatedProxyDownload(
                                            `/api/direct-download/${encodeURIComponent(
                                              zipName
                                            )}?driveFileId=${encodeURIComponent(file.id)}&compress=zip${
                                              personalEmail ? `&userEmail=${encodeURIComponent(personalEmail)}` : ''
                                            }${personalChatId ? `&chatId=${encodeURIComponent(personalChatId)}` : ''}`,
                                            zipName,
                                            zipItemKey
                                          )
                                        }
                                        className="px-2.5 py-1 rounded-lg bg-emerald-500/15 hover:bg-emerald-500/25 text-emerald-300 font-semibold flex items-center gap-1 cursor-pointer disabled:opacity-50"
                                        title={`ضغط ZIP بدون فقدان الجودة (توفير ~${zipCheck.zipSavedPercent}%)`}
                                      >
                                        {downloadingItemId === zipItemKey ? (
                                          <Loader2 className="w-3 h-3 animate-spin" />
                                        ) : (
                                          <Download className="w-3 h-3" />
                                        )}
                                        <span>ZIP (-{zipCheck.zipSavedPercent}%)</span>
                                      </button>
                                    );
                                  })()}

                                  <button
                                    onClick={() => copyLink(file.id, file.webViewLink)}
                                    className="p-1.5 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-300 cursor-pointer"
                                    title="نسخ الرابط"
                                  >
                                    {copiedId === file.id ? (
                                      <Check className="w-3.5 h-3.5 text-emerald-400" />
                                    ) : (
                                      <Copy className="w-3.5 h-3.5" />
                                    )}
                                  </button>

                                  {confirmDeleteId === file.id ? (
                                    <button
                                      onClick={() => handleDeleteDriveFile(file.id)}
                                      className="px-2 py-1 rounded bg-rose-600 text-white font-bold cursor-pointer"
                                    >
                                      تأكيد
                                    </button>
                                  ) : (
                                    <button
                                      onClick={() => setConfirmDeleteId(file.id)}
                                      className="p-1.5 rounded-lg bg-slate-800 hover:bg-rose-950/60 text-slate-400 hover:text-rose-300 cursor-pointer"
                                    >
                                      <Trash2 className="w-3.5 h-3.5" />
                                    </button>
                                  )}
                                </div>
                              </div>
                            ))}
                          </div>
                        )}
                      </div>
                    </>
                  )}
                </div>
              )}

              {/* MODAL 3: LARGE LOCAL FILE UPLOAD */}
              {activeModal === 'large_upload' && (
                <div className="space-y-4">
                  <p className="text-xs text-slate-400">
                    رفع مباشر مقسم (Resumable Chunked Upload) من متصفحك إلى حسابك الشخصي في Google Drive لأي حجم (1GB أو 10GB+).
                  </p>

                  {!accessToken ? (
                    <div className="p-8 rounded-xl bg-slate-900/60 border border-slate-800 text-center space-y-3">
                      <p className="text-sm text-slate-300">يرجى تسجيل الدخول بحسابك في Google Drive أولاً لتفعيل الرفع المباشر.</p>
                      <button
                        onClick={handleSignIn}
                        className="px-5 py-2 rounded-xl bg-sky-600 hover:bg-sky-500 text-white font-semibold text-xs transition cursor-pointer"
                      >
                        تسجيل الدخول بـ Google
                      </button>
                    </div>
                  ) : (
                    <label className="block border-2 border-dashed border-slate-700 hover:border-indigo-500/60 rounded-2xl p-8 sm:p-10 text-center cursor-pointer transition bg-slate-900/40">
                      <input
                        type="file"
                        className="hidden"
                        disabled={uploadingLocal}
                        onChange={handleDirectLargeFileUpload}
                      />
                      {uploadingLocal ? (
                        <div className="space-y-3 max-w-md mx-auto">
                          <div className="flex items-center justify-between text-xs text-indigo-300 font-semibold">
                            <span className="truncate">{localUploadFileName}</span>
                            <span className="tabular-nums">{localUploadProgress}%</span>
                          </div>
                          <div className="w-full h-2.5 bg-slate-800 rounded-full overflow-hidden">
                            <div
                              className="h-full bg-indigo-500 transition-all duration-200"
                              style={{ width: `${localUploadProgress}%` }}
                            />
                          </div>
                          <p className="text-xs text-slate-400">جاري الرفع المباشر إلى مجلد "{selectedFolderName}"...</p>
                        </div>
                      ) : (
                        <div className="space-y-2">
                          <UploadCloud className="w-10 h-10 text-indigo-400 mx-auto" />
                          <p className="text-sm font-bold text-white">اضغط هنا لاختيار أي ملف ضخم من جهازك</p>
                          <p className="text-xs text-slate-400">
                            سيتم حفظه في مجلد: <strong className="text-emerald-300">{selectedFolderName}</strong>
                          </p>
                        </div>
                      )}
                    </label>
                  )}
                </div>
              )}

              {/* MODAL 4: PERSONAL ACCOUNT & SETTINGS */}
              {activeModal === 'settings' && (
                <div className="space-y-5">
                  {unauthorizedDomainHost && (
                    <div className="p-4 rounded-xl bg-amber-950/60 border border-amber-500/40 space-y-3 text-xs">
                      <p className="font-bold text-amber-200 text-sm">
                        لماذا ظهر خطأ (origin_mismatch) على دومين Vercel ({unauthorizedDomainHost})؟ وكيف تربط حسابك فوراً؟
                      </p>
                      <p className="text-amber-100/90 leading-relaxed">
                        أمان Google OAuth يمنع فتح نافذة الدخول على أي رابط جديد غير مسجل. لديك <strong>حلّان</strong>:
                      </p>
                      <div className="p-3 rounded-lg bg-slate-950/90 border border-emerald-500/30 space-y-2">
                        <p className="font-bold text-emerald-300">
                          الحل الأول (فوري في ثانيتين بدون إعدادات Google Cloud):
                        </p>
                        <p className="text-slate-300">
                          من تبويب البرنامج هنا في AI Studio اضغط <strong>"نسخ كود تفعيل الجلسة السريع لـ Vercel"</strong> أو أدخل رابط موقعك على Vercel واضغط <strong>"ربط موقع Vercel بحسابي الآن"</strong>، أو الصق الكود في الخانة أدناه!
                        </p>
                      </div>
                      <div className="p-3 rounded-lg bg-slate-950/90 border border-amber-500/30 space-y-2.5">
                        <p className="font-bold text-amber-300">
                          الحل الثاني (لتفعيل زر الدخول المباشر من Google على دومين Vercel نهائياً):
                        </p>
                        <div className="space-y-1.5">
                          <span className="text-slate-300 block">
                            1. أضف هذا النطاق في{' '}
                            <a
                              href={`https://console.firebase.google.com/project/${(firebaseConfig as any).projectId}/authentication/settings`}
                              target="_blank"
                              rel="noreferrer"
                              className="text-sky-400 underline font-semibold"
                            >
                              Firebase Authorized Domains
                            </a>
                            :
                          </span>
                          <div className="flex items-center justify-between gap-2 p-2 rounded-lg bg-slate-900 border border-slate-800">
                            <code className="text-amber-300 font-mono truncate" dir="ltr">
                              {unauthorizedDomainHost}
                            </code>
                            <button
                              type="button"
                              onClick={() => {
                                navigator.clipboard.writeText(unauthorizedDomainHost);
                                setCopiedDomain(true);
                                setTimeout(() => setCopiedDomain(false), 2000);
                              }}
                              className="px-2.5 py-1 rounded bg-amber-500/20 hover:bg-amber-500/30 text-amber-200 font-semibold cursor-pointer shrink-0"
                            >
                              {copiedDomain ? 'تم النسخ' : 'نسخ النطاق'}
                            </button>
                          </div>
                        </div>

                        <div className="space-y-1.5">
                          <span className="text-slate-300 block">
                            2. أضف هذا الرابط في{' '}
                            <a
                              href={`https://console.cloud.google.com/apis/credentials?project=${(firebaseConfig as any).projectId}`}
                              target="_blank"
                              rel="noreferrer"
                              className="text-sky-400 underline font-semibold"
                            >
                              Google Cloud Credentials (Authorized JavaScript origins)
                            </a>
                            :
                          </span>
                          <div className="flex items-center justify-between gap-2 p-2 rounded-lg bg-slate-900 border border-slate-800">
                            <code className="text-emerald-300 font-mono truncate" dir="ltr">
                              {window.location.origin}
                            </code>
                            <button
                              type="button"
                              onClick={() => {
                                navigator.clipboard.writeText(window.location.origin);
                                setCopiedOrigin(true);
                                setTimeout(() => setCopiedOrigin(false), 2000);
                              }}
                              className="px-2.5 py-1 rounded bg-emerald-500/20 hover:bg-emerald-500/30 text-emerald-200 font-semibold cursor-pointer shrink-0"
                            >
                              {copiedOrigin ? 'تم النسخ' : 'نسخ الرابط الكامل'}
                            </button>
                          </div>
                        </div>
                      </div>
                    </div>
                  )}

                  <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                    {/* Google Drive Account Box */}
                    <div className="p-4 rounded-xl bg-slate-900/70 border border-slate-800 space-y-3">
                      <div className="flex items-center justify-between">
                        <span className="text-xs font-bold text-white">حساب Google Drive الشخصي</span>
                        <span className={`text-xs font-semibold ${driveConnected ? 'text-emerald-400' : 'text-amber-400'}`}>
                          {driveConnected ? 'متصل' : 'غير مربوط'}
                        </span>
                      </div>
                      <p className="text-xs text-slate-400 font-mono truncate">
                        {effectiveUserEmail || 'لم يتم ربط بريد Google بعد'}
                      </p>
                      <div className="flex flex-wrap gap-2 pt-1">
                        <button
                          onClick={handleSignIn}
                          className="px-3.5 py-2 rounded-lg bg-sky-600 hover:bg-sky-500 text-white text-xs font-semibold transition cursor-pointer"
                        >
                          {driveConnected ? 'تبديل حساب Google' : 'ربط حساب Google Drive'}
                        </button>
                        {driveConnected && (
                          <>
                            <button
                              onClick={() =>
                                handleUpdateSettings({
                                  accountEnabled: !(serverStatus?.drive.accountEnabled ?? true),
                                })
                              }
                              disabled={savingSettings}
                              className="px-3 py-2 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-200 text-xs font-semibold transition cursor-pointer"
                            >
                              {serverStatus?.drive.accountEnabled !== false ? 'إيقاف مؤقت' : 'تفعيل الاستقبال'}
                            </button>
                            <button
                              onClick={handleDisconnectDrive}
                              className="px-3 py-2 rounded-lg bg-rose-500/15 hover:bg-rose-500/25 text-rose-300 text-xs font-semibold transition cursor-pointer"
                            >
                              إلغاء الربط
                            </button>
                          </>
                        )}
                      </div>

                      {/* Quick Session Code Paste Box for Instant Vercel Linking */}
                      <div className="pt-2 border-t border-slate-800/80 space-y-2">
                        <label className="block text-[11px] font-semibold text-slate-300">
                          ربط فوري على Vercel بكود الجلسة (يتجاوز خطأ origin_mismatch بدون إعدادات):
                        </label>
                        <div className="flex items-center gap-1.5">
                          <input
                            type="text"
                            dir="ltr"
                            value={sessionCodeInput}
                            onChange={(e) => setSessionCodeInput(e.target.value)}
                            placeholder="الصق كود الجلسة TD1_... هنا"
                            className="flex-1 px-2.5 py-1.5 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                          />
                          <button
                            type="button"
                            disabled={applyingSessionCode || !sessionCodeInput.trim()}
                            onClick={() => applyPortableSessionCode(sessionCodeInput)}
                            className="px-3 py-1.5 rounded-lg bg-emerald-600 hover:bg-emerald-500 disabled:opacity-50 text-white text-xs font-bold cursor-pointer shrink-0 flex items-center gap-1"
                          >
                            {applyingSessionCode ? <Loader2 className="w-3.5 h-3.5 animate-spin" /> : <Check className="w-3.5 h-3.5" />}
                            <span>تفعيل</span>
                          </button>
                        </div>
                      </div>
                    </div>

                    {/* Telegram Link Box */}
                    <div className="p-4 rounded-xl bg-slate-900/70 border border-slate-800 space-y-3">
                      <div className="flex items-center justify-between">
                        <span className="text-xs font-bold text-white">ربط محادثتك في تليجرام</span>
                        <span className={`text-xs font-semibold ${linkedChatId ? 'text-indigo-400' : 'text-slate-400'}`}>
                          {linkedChatId ? `مربوط (#${linkedChatId})` : 'غير مربوط'}
                        </span>
                      </div>

                      {linkCode && (
                        <div className="flex items-center justify-between gap-2 p-2 rounded-lg bg-slate-950 border border-slate-800 text-xs">
                          <code className="text-amber-300 font-mono truncate" dir="ltr">
                            /start link_{linkCode}
                          </code>
                          <button
                            onClick={() => {
                              navigator.clipboard.writeText(`/start link_${linkCode}`);
                              setCopiedLinkCode(true);
                              setTimeout(() => setCopiedLinkCode(false), 2000);
                            }}
                            className="px-2 py-1 rounded bg-slate-800 hover:bg-slate-700 text-[11px] text-slate-200 cursor-pointer shrink-0"
                          >
                            {copiedLinkCode ? 'تم النسخ' : 'نسخ الرمز'}
                          </button>
                        </div>
                      )}

                      <div className="flex flex-wrap gap-2 pt-1">
                        {botUsername && (
                          <a
                            href={telegramDeepLink}
                            target="_blank"
                            rel="noreferrer"
                            className="px-3.5 py-2 rounded-lg bg-indigo-600 hover:bg-indigo-500 text-white text-xs font-semibold transition inline-flex items-center gap-1.5"
                          >
                            <Bot className="w-3.5 h-3.5" />
                            <span>فتح البوت وربط تليجرام</span>
                          </a>
                        )}
                        {linkedChatId && (
                          <button
                            onClick={() => {
                              localStorage.removeItem(STORAGE_CHAT_ID_KEY);
                              setPersonalChatId('');
                              handleUpdateSettings({ unlinkTelegramChat: true });
                            }}
                            className="px-3 py-2 rounded-lg bg-slate-800 hover:bg-rose-950/50 text-slate-300 hover:text-rose-300 text-xs font-semibold transition cursor-pointer"
                          >
                            فصل المحادثة
                          </button>
                        )}
                      </div>
                    </div>
                  </div>

                  {/* 1-Click Vercel Remote Sync Bridge (When Drive is Connected here) */}
                  {driveConnected && (
                    <div className="p-4 rounded-xl bg-emerald-950/30 border border-emerald-500/30 space-y-3">
                      <div className="flex flex-wrap items-center justify-between gap-2">
                        <div>
                          <p className="text-xs font-bold text-emerald-300 flex items-center gap-1.5">
                            <Globe className="w-4 h-4 text-emerald-400" />
                            <span>ربط وتفعيل موقعك على Vercel بحسابك الحالي بضغطة واحدة</span>
                          </p>
                          <p className="text-[11px] text-slate-400 mt-0.5">
                            انقل جلسة Google Drive ({effectiveUserEmail}) إلى موقعك على Vercel مباشرة بدون الحاجة لإعدادات Google Cloud:
                          </p>
                        </div>
                        <button
                          type="button"
                          onClick={handleCopyPortableSessionCode}
                          className="px-3 py-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 border border-emerald-500/40 text-emerald-300 text-xs font-semibold flex items-center gap-1.5 cursor-pointer shrink-0"
                        >
                          {copiedSessionCode ? <Check className="w-3.5 h-3.5" /> : <Copy className="w-3.5 h-3.5" />}
                          <span>{copiedSessionCode ? 'تم نسخ الكود!' : 'نسخ كود تفعيل الجلسة'}</span>
                        </button>
                      </div>

                      <form onSubmit={handlePushSessionToVercel} className="flex flex-col sm:flex-row gap-2">
                        <input
                          type="text"
                          dir="ltr"
                          value={targetVercelUrl}
                          onChange={(e) => setTargetVercelUrl(e.target.value)}
                          placeholder="https://your-project.vercel.app (رابط موقعك على Vercel)"
                          className="flex-1 px-3 py-2 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                        />
                        <button
                          type="submit"
                          disabled={pushingToVercel}
                          className="px-4 py-2 rounded-lg bg-emerald-600 hover:bg-emerald-500 disabled:opacity-50 text-white text-xs font-bold flex items-center justify-center gap-1.5 cursor-pointer shrink-0"
                        >
                          {pushingToVercel ? (
                            <Loader2 className="w-3.5 h-3.5 animate-spin" />
                          ) : (
                            <Send className="w-3.5 h-3.5" />
                          )}
                          <span>ربط موقع Vercel الآن وإرسال الرابط لتليجرام</span>
                        </button>
                      </form>

                      {magicLoginUrlResult && (
                        <div className="pt-1 flex items-center justify-between gap-2 p-2.5 rounded-lg bg-slate-950 border border-emerald-500/40 text-xs">
                          <span className="text-emerald-300 font-semibold truncate">
                            تم الربط! افتح موقعك على Vercel بالحساب جاهزاً:
                          </span>
                          <a
                            href={magicLoginUrlResult}
                            target="_blank"
                            rel="noreferrer"
                            className="px-3 py-1 rounded bg-emerald-600 hover:bg-emerald-500 text-white font-bold flex items-center gap-1 shrink-0"
                          >
                            <span>فتح موقعي على Vercel</span>
                            <ExternalLink className="w-3.5 h-3.5" />
                          </a>
                        </div>
                      )}
                    </div>
                  )}

                  {/* Preferences */}
                  <div className="grid grid-cols-1 sm:grid-cols-3 gap-3">
                    <div className="p-3.5 rounded-xl bg-slate-900/60 border border-slate-800 flex items-center justify-between gap-2">
                      <div>
                        <p className="text-xs font-bold text-white">الفرز التلقائي للمجلدات</p>
                        <p className="text-[11px] text-slate-400">حسب نوع الملف</p>
                      </div>
                      <button
                        onClick={handleToggleAutoCategorize}
                        className={`px-3 py-1 rounded-lg text-xs font-bold cursor-pointer ${
                          autoCategorize ? 'bg-emerald-500/20 text-emerald-300' : 'bg-slate-800 text-slate-400'
                        }`}
                      >
                        {autoCategorize ? 'مفعل' : 'معطل'}
                      </button>
                    </div>

                    <div className="p-3.5 rounded-xl bg-slate-900/60 border border-slate-800 flex items-center justify-between gap-2">
                      <div>
                        <p className="text-xs font-bold text-white">منع تكرار الملفات</p>
                        <p className="text-[11px] text-slate-400">تخطي الموجود مسبقاً</p>
                      </div>
                      <button
                        onClick={handleToggleSkipDuplicates}
                        className={`px-3 py-1 rounded-lg text-xs font-bold cursor-pointer ${
                          skipDuplicates ? 'bg-emerald-500/20 text-emerald-300' : 'bg-slate-800 text-slate-400'
                        }`}
                      >
                        {skipDuplicates ? 'مفعل' : 'معطل'}
                      </button>
                    </div>

                    <div className="p-3.5 rounded-xl bg-slate-900/60 border border-slate-800 space-y-1.5">
                      <p className="text-xs font-bold text-white">الجودة الافتراضية لبوت تليجرام</p>
                      <select
                        value={serverStatus?.drive.defaultQuality || '720'}
                        onChange={(e) => handleUpdateSettings({ defaultQuality: e.target.value })}
                        className="w-full px-2.5 py-1 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white"
                      >
                        <option value="1080">1080p Full HD</option>
                        <option value="720">720p HD</option>
                        <option value="480">480p</option>
                        <option value="360">360p</option>
                        <option value="240">240p</option>
                      </select>
                    </div>
                  </div>

                  {/* Optional Custom Google Client ID for Vercel */}
                  <div className="p-3.5 rounded-xl bg-slate-900/40 border border-slate-800/80 space-y-2">
                    <label className="block text-xs font-semibold text-slate-300">
                      معرف عميل Google OAuth مخصص لـ Vercel (اختياري - Client ID)
                    </label>
                    <input
                      type="text"
                      dir="ltr"
                      value={customClientId}
                      onChange={(e) => {
                        setCustomClientId(e.target.value);
                        localStorage.setItem(STORAGE_CUSTOM_CLIENT_ID_KEY, e.target.value.trim());
                      }}
                      placeholder="xxxx.apps.googleusercontent.com (اتركه فارغاً للافتراضي)"
                      className="w-full px-3 py-1.5 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                    />
                  </div>

                  {(personalEmail || personalChatId) && (
                    <div className="pt-2 border-t border-slate-800 flex justify-end">
                      <button
                        onClick={handleClearPersonalSession}
                        className="px-3.5 py-2 rounded-lg bg-slate-900 hover:bg-rose-950/40 text-slate-400 hover:text-rose-300 border border-slate-800 text-xs transition flex items-center gap-1.5 cursor-pointer"
                      >
                        <LogOut className="w-3.5 h-3.5" />
                        <span>الخروج من الجلسة على هذا المتصفح</span>
                      </button>
                    </div>
                  )}
                </div>
              )}

              {/* MODAL 5: OWNER ADMIN & VERCEL DEPLOYMENT */}
              {activeModal === 'admin' && (
                <div className="space-y-5">
                  <div className="flex flex-wrap items-center justify-between gap-3 p-4 rounded-xl bg-slate-900/60 border border-slate-800">
                    <div className="space-y-0.5">
                      <p className="text-xs font-bold text-white">
                        حالة البوت: {botConnected ? 'متصل ويعمل' : 'غير متصل'} · محرك MTProto 2GB: {mtprotoConnected ? 'مفعل' : 'قياسي'}
                      </p>
                      <p className="text-[11px] text-slate-400">
                        وضع الوصول الحالي: {serverStatus?.admin?.accessMode === 'owner_only' ? 'خاص بالمالك فقط' : 'عام لجميع المستخدمين'}
                      </p>
                    </div>

                    <div className="flex flex-wrap items-center gap-2">
                      <button
                        onClick={() =>
                          handleUpdateSettings({
                            accessMode: serverStatus?.admin?.accessMode === 'owner_only' ? 'public' : 'owner_only',
                          })
                        }
                        className="px-3 py-1.5 rounded-lg bg-amber-500/15 hover:bg-amber-500/25 text-amber-300 text-xs font-semibold cursor-pointer"
                      >
                        تبديل وضع الوصول
                      </button>

                      <button
                        onClick={() => handleUpdateSettings({ botPaused: !serverStatus?.admin?.botPaused })}
                        className={`px-3 py-1.5 rounded-lg text-xs font-bold flex items-center gap-1 cursor-pointer ${
                          serverStatus?.admin?.botPaused
                            ? 'bg-emerald-600 text-white'
                            : 'bg-rose-500/20 text-rose-300'
                        }`}
                      >
                        <Power className="w-3.5 h-3.5" />
                        <span>{serverStatus?.admin?.botPaused ? 'تشغيل البوت' : 'إيقاف مؤقت'}</span>
                      </button>
                    </div>
                  </div>

                  {/* Vercel Webhook Card */}
                  <div className="p-4 rounded-xl bg-slate-900/80 border border-sky-500/30 space-y-3">
                    <div className="flex flex-wrap items-center justify-between gap-2">
                      <h3 className="text-xs font-bold text-white flex items-center gap-1.5">
                        <Globe className="w-4 h-4 text-sky-400" />
                        <span>تشغيل البوت على منصة Vercel (Webhook)</span>
                      </h3>
                      <span className="text-xs text-sky-300 font-medium">
                        {serverStatus?.deployment?.mode === 'webhook' ? 'وضع Webhook نشط' : 'وضع Polling مباشر'}
                      </span>
                    </div>

                    <div className="p-2.5 rounded-lg bg-slate-950 border border-slate-800 text-xs">
                      <span className="text-slate-400 block mb-1">رابط الـ Webhook:</span>
                      <code className="text-emerald-300 font-mono break-all" dir="ltr">
                        {serverStatus?.deployment?.webhookUrl || `${window.location.origin}/api/telegram/webhook`}
                      </code>
                    </div>

                    <div className="flex flex-wrap items-center gap-2">
                      <button
                        onClick={handleActivateVercelWebhook}
                        disabled={reconnectingBot}
                        className="px-3.5 py-2 rounded-lg bg-sky-600 hover:bg-sky-500 text-white text-xs font-bold flex items-center gap-1.5 cursor-pointer"
                      >
                        <Link2 className="w-3.5 h-3.5" />
                        <span>تفعيل Webhook على هذا الرابط</span>
                      </button>
                      <button
                        onClick={handleReconnectBot}
                        disabled={reconnectingBot}
                        className="px-3.5 py-2 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-200 text-xs font-semibold flex items-center gap-1.5 cursor-pointer"
                      >
                        <RefreshCw className={`w-3.5 h-3.5 ${reconnectingBot ? 'animate-spin' : ''}`} />
                        <span>إعادة تنشيط الاتصال و MTProto</span>
                      </button>
                    </div>
                  </div>

                  {/* Connected Users List */}
                  <div className="space-y-2">
                    <h4 className="text-xs font-bold text-slate-300">
                      المستخدمون المتصلون ({serverStatus?.admin?.knownUsers?.length || 0})
                    </h4>
                    {!serverStatus?.admin?.knownUsers || serverStatus.admin.knownUsers.length === 0 ? (
                      <p className="text-xs text-slate-500">لا يوجد مستخدمون مسجلون بعد.</p>
                    ) : (
                      <div className="grid grid-cols-1 sm:grid-cols-2 gap-2 max-h-48 overflow-y-auto">
                        {serverStatus.admin.knownUsers.map((u) => (
                          <div
                            key={u.chatId}
                            className="p-3 rounded-xl bg-slate-900/70 border border-slate-800 flex items-center justify-between gap-2"
                          >
                            <div className="min-w-0">
                              <p className="text-xs font-bold text-white truncate">
                                {u.name} {u.username ? `(@${u.username})` : ''}
                              </p>
                              <p className="text-[11px] text-slate-400 font-mono tabular-nums">
                                #{u.chatId} · {u.transfersCount} عملية
                              </p>
                            </div>
                            {u.chatId !== serverStatus.admin?.ownerChatId && (
                              <button
                                onClick={() => handleUpdateSettings({ toggleBlockChatId: u.chatId })}
                                className={`px-2.5 py-1 rounded-lg text-xs font-semibold shrink-0 cursor-pointer ${
                                  u.blocked
                                    ? 'bg-emerald-500/15 text-emerald-300'
                                    : 'bg-rose-500/15 text-rose-300'
                                }`}
                              >
                                {u.blocked ? 'فك الحظر' : 'حظر'}
                              </button>
                            )}
                          </div>
                        ))}
                      </div>
                    )}
                  </div>
                </div>
              )}
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
