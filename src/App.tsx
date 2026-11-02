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
  Folder,
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

type CompressMode = 'none' | 'zip' | 'media';
type ModalType = 'drive_files' | 'large_upload' | 'settings' | 'admin' | 'url_options' | null;

interface TransferJob {
  id: string;
  source?: 'telegram' | 'url' | 'web' | 'drive_to_telegram' | 'url_to_telegram';
  direction?: 'to_drive' | 'to_telegram';
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

  // Custom Google Client ID support (for Vercel deployments)
  const [customClientId, setCustomClientId] = useState<string>(() => {
    return localStorage.getItem(STORAGE_CUSTOM_CLIENT_ID_KEY) || '';
  });
  const [unauthorizedDomainHost, setUnauthorizedDomainHost] = useState<string | null>(null);
  const [copiedDomain, setCopiedDomain] = useState(false);

  // Google OAuth state
  const [accessToken, setAccessToken] = useState<string | null>(null);
  const [userProfile, setUserProfile] = useState<{ name: string; email: string; picture?: string } | null>(null);
  const tokenClientRef = useRef<any>(null);

  // Server & Bot state
  const [serverStatus, setServerStatus] = useState<ServerStatus | null>(null);
  const [reconnectingBot, setReconnectingBot] = useState(false);
  const [autoCategorize, setAutoCategorize] = useState(true);
  const [skipDuplicates, setSkipDuplicates] = useState(true);

  // Popup Modal State (All menus hidden inside popup modals)
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

  // Multi-platform URL Uploader state
  const [externalUrlInput, setExternalUrlInput] = useState('');
  const [externalCustomName, setExternalCustomName] = useState('');
  const [externalDestination, setExternalDestination] = useState<'drive' | 'telegram' | 'device'>('drive');
  const [externalMediaFormat, setExternalMediaFormat] = useState<'video' | 'audio'>('video');
  const [externalQuality, setExternalQuality] = useState<string>('720');
  const [externalCompressMode, setExternalCompressMode] = useState<CompressMode>('none');
  const [submittingUrl, setSubmittingUrl] = useState(false);
  const [clearingFailed, setClearingFailed] = useState(false);

  // Alerts
  const [bannerError, setBannerError] = useState<string | null>(null);
  const [bannerSuccess, setBannerSuccess] = useState<string | null>(null);

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
    } catch {
      // Ignore transient poll errors
    }
  }, [buildIdentityQuery, selectedFolderId, personalChatId]);

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
    const data = await res.json();
    if (!res.ok) {
      throw new Error(data.error || 'تعذر مزامنة جلسة حسابك مع الخادم.');
    }
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
      if (tokenClientRef.current) {
        tokenClientRef.current.requestAccessToken({ prompt: 'select_account' });
        return;
      }
      if (err?.code === 'auth/unauthorized-domain') {
        const currentHost = window.location.hostname;
        setUnauthorizedDomainHost(currentHost);
        setActiveModal('settings');
        setBannerError(
          `النطاق (${currentHost}) غير مضاف بعد في قائمة النطاقات المصرح بها في Firebase. راجع الخطوة الموضحة في نافذة الإعدادات.`
        );
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

  const handleUrlUploadSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!externalUrlInput.trim()) return;

    if (externalDestination === 'device') {
      const q = new URLSearchParams({
        url: externalUrlInput.trim(),
        format: externalMediaFormat,
        quality: externalQuality,
        compress: externalCompressMode,
      });
      if (externalCustomName.trim()) {
        q.set('name', externalCustomName.trim());
      }
      if (personalEmail) q.set('userEmail', personalEmail);
      if (personalChatId) q.set('chatId', personalChatId);
      const downloadHref = `/api/direct-download?${q.toString()}`;
      const a = document.createElement('a');
      a.href = downloadHref;
      a.download = externalCustomName.trim() || '';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      setBannerSuccess('بدأ تحضير وتحميل الملف مباشرة إلى جهازك عبر المتصفح!');
      setTimeout(() => setBannerSuccess(null), 4000);
      return;
    }

    setSubmittingUrl(true);
    setBannerError(null);
    try {
      const headers: Record<string, string> = { 'Content-Type': 'application/json' };
      if (accessToken) {
        headers.Authorization = `Bearer ${accessToken}`;
      }
      const res = await fetch('/api/transfers/url', {
        method: 'POST',
        headers,
        body: JSON.stringify({
          url: externalUrlInput.trim(),
          customFileName: externalCustomName.trim() || undefined,
          destination: externalDestination,
          mediaFormat: externalMediaFormat,
          quality: externalQuality,
          compressMode: externalCompressMode,
          userEmail: personalEmail || undefined,
          targetChatId: personalChatId || undefined,
        }),
      });
      const data = await res.json();
      if (!res.ok) {
        throw new Error(data.error || 'تعذر إضافة الرابط للتحويل.');
      }
      setExternalUrlInput('');
      setExternalCustomName('');
      setBannerSuccess(
        externalDestination === 'telegram'
          ? 'تم بدء سحب الرابط وإرساله كملف إلى محادثتك في تليجرام!'
          : 'تمت إضافة الرابط لطابور الرفع إلى حسابك الشخصي في Google Drive!'
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
      const data = await res.json();
      if (!res.ok) {
        throw new Error(data.error || 'تعذر إرسال الملف إلى تليجرام.');
      }
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
      const data = await res.json();
      if (!res.ok) {
        throw new Error(data.error || 'تعذر حفظ الإعدادات.');
      }
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
      const data = await res.json();
      if (res.ok) {
        setBannerSuccess(`تم حذف ${data.removedCount} من الملفات الفاشلة والملغاة من سجلك.`);
        setTimeout(() => setBannerSuccess(null), 3500);
      }
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
      const data = await res.json();
      if (!res.ok) {
        throw new Error(data.error || 'تعذر تفعيل Webhook.');
      }
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

  const compressLabel =
    externalCompressMode === 'zip' ? 'ZIP' : externalCompressMode === 'media' ? 'ضغط FFmpeg' : 'بدون ضغط';

  return (
    <div dir="rtl" className="min-h-screen bg-[#090D16] text-slate-100 font-sans flex flex-col">
      {/* Single Clean Top Bar — Fits 100% on Mobile & Desktop Without Truncation or Disappearing Links */}
      <header className="px-3 sm:px-6 py-3 border-b border-slate-800/80 bg-[#0D1322]/95 backdrop-blur-md sticky top-0 z-30">
        <div className="max-w-5xl mx-auto flex items-center justify-between gap-2 sm:gap-6">
          {/* Zone 1: Brand Title */}
          <div className="flex items-center gap-2 shrink-0">
            <div className="w-7 h-7 sm:w-8 sm:h-8 rounded-lg bg-sky-500/15 border border-sky-500/30 flex items-center justify-center text-sky-400">
              <Send className="w-3.5 h-3.5 sm:w-4 sm:h-4" />
            </div>
            <span className="text-sm sm:text-base font-bold text-white tracking-tight whitespace-nowrap">
              TeleDrive
            </span>
          </div>

          {/* Zone 2: Popup Menu Links (Always Visible on Mobile & Desktop) */}
          <nav className="flex items-center gap-1 sm:gap-2">
            <button
              onClick={() => {
                setActiveModal('drive_files');
                if (accessToken) refreshDriveFoldersAndFiles();
              }}
              className="px-2 sm:px-3 py-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 border border-slate-800 text-slate-200 text-xs font-medium flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap shrink-0"
            >
              <HardDrive className="w-3.5 h-3.5 text-sky-400 shrink-0" />
              <span>ملفاتي</span>
            </button>

            <button
              onClick={() => setActiveModal('large_upload')}
              className="px-2 sm:px-3 py-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 border border-slate-800 text-slate-200 text-xs font-medium flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap shrink-0"
            >
              <UploadCloud className="w-3.5 h-3.5 text-indigo-400 shrink-0" />
              <span>رفع ضخم</span>
            </button>

            <button
              onClick={() => setActiveModal('admin')}
              className="px-2 sm:px-3 py-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 border border-slate-800 text-slate-200 text-xs font-medium flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap shrink-0"
            >
              <ShieldAlert className="w-3.5 h-3.5 text-amber-400 shrink-0" />
              <span>الإدارة</span>
            </button>
          </nav>

          {/* Zone 3: Single Unified Account & Settings Popup Trigger */}
          <button
            onClick={() => setActiveModal('settings')}
            className={`px-2.5 sm:px-3.5 py-1.5 rounded-lg text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap shrink-0 ${
              driveConnected
                ? 'bg-emerald-500/15 hover:bg-emerald-500/25 text-emerald-300 border border-emerald-500/30'
                : 'bg-sky-600 hover:bg-sky-500 text-white'
            }`}
          >
            <User className="w-3.5 h-3.5 shrink-0" />
            <span>{driveConnected ? 'حسابي متصل' : 'ربط الحساب'}</span>
          </button>
        </div>
      </header>

      {/* Main Focused Workspace */}
      <main className="flex-1 max-w-5xl w-full mx-auto px-3.5 sm:px-6 py-4 sm:py-6 space-y-4 sm:space-y-5">
        {/* Notification Banners */}
        {bannerError && (
          <div className="p-3.5 rounded-xl bg-rose-950/70 border border-rose-500/40 text-rose-200 flex items-center justify-between gap-3">
            <div className="flex items-center gap-2.5 text-xs sm:text-sm">
              <AlertTriangle className="w-4 h-4 text-rose-400 shrink-0" />
              <span>{bannerError}</span>
            </div>
            <button onClick={() => setBannerError(null)} className="text-xs text-rose-300 hover:text-white shrink-0 cursor-pointer">
              إغلاق
            </button>
          </div>
        )}

        {bannerSuccess && (
          <div className="p-3.5 rounded-xl bg-emerald-950/70 border border-emerald-500/40 text-emerald-200 flex items-center justify-between gap-3">
            <div className="flex items-center gap-2.5 text-xs sm:text-sm">
              <CheckCircle2 className="w-4 h-4 text-emerald-400 shrink-0" />
              <span>{bannerSuccess}</span>
            </div>
            <button onClick={() => setBannerSuccess(null)} className="text-xs text-emerald-300 hover:text-white shrink-0 cursor-pointer">
              إغلاق
            </button>
          </div>
        )}

        {/* Interactive Status Bar (Opens Settings or Drive Folder Popup When Clicked) */}
        <div
          onClick={() => setActiveModal('settings')}
          className="px-4 py-3 rounded-xl bg-[#0D1322] hover:bg-slate-900/90 border border-slate-800/90 flex flex-wrap items-center justify-between gap-2 text-xs text-slate-400 cursor-pointer transition"
        >
          <div className="flex flex-wrap items-center gap-x-2 gap-y-1">
            <span className={driveConnected ? 'text-emerald-300 font-semibold' : 'text-amber-300 font-semibold'}>
              {driveConnected
                ? `Google Drive: ${effectiveUserEmail || effectiveUserName}`
                : 'اضغط هنا لربط Google Drive وتليجرام'}
            </span>
            <span aria-hidden="true">·</span>
            <span>
              المجلد: <strong className="text-slate-200">{serverStatus?.drive.activeFolderName || selectedFolderName}</strong>
            </span>
            <span aria-hidden="true">·</span>
            <span>
              تليجرام: <strong className="text-slate-200">{linkedChatId ? `مربوط (#${linkedChatId})` : 'غير مربوط'}</strong>
            </span>
          </div>

          <div className="flex items-center gap-2 tabular-nums text-slate-300">
            <span>المكتملة: {serverStatus?.stats.completedJobs ?? 0}</span>
            <span aria-hidden="true">·</span>
            <span>الجارية: {serverStatus?.stats.activeJobs ?? 0}</span>
            <span aria-hidden="true">·</span>
            <span dir="ltr">{formatBytes(serverStatus?.stats.totalBytesTransferred ?? 0)}</span>
          </div>
        </div>

        {/* Core Card 1: Multi-Platform URL & Video Puller */}
        <section className="bg-[#0D1322] border border-slate-800/90 rounded-2xl p-4 sm:p-6 space-y-4">
          <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-3">
            <div>
              <h1 className="text-base sm:text-lg font-bold text-white">
                سحب وتحميل الفيديوهات والملفات عبر الروابط
              </h1>
              <p className="text-xs text-slate-400 mt-0.5">
                يدعم YouTube و TikTok و Google Drive و MediaFire و Dropbox والروابط المباشرة
              </p>
            </div>

            {/* Popup Trigger for Extraction Quality & Compression Options */}
            <button
              type="button"
              onClick={() => setActiveModal('url_options')}
              className="self-start sm:self-auto px-3 py-1.5 rounded-xl bg-slate-900 hover:bg-slate-800 border border-slate-700/80 text-slate-200 text-xs font-medium flex items-center gap-2 transition cursor-pointer whitespace-nowrap shrink-0"
            >
              <Sliders className="w-3.5 h-3.5 text-sky-400 shrink-0" />
              <span>
                خيارات السحب: {externalMediaFormat === 'audio' ? `MP3 (${externalQuality}k)` : `MP4 (${externalQuality}p)`} · {compressLabel}
              </span>
            </button>
          </div>

          <form onSubmit={handleUrlUploadSubmit} className="space-y-3.5">
            {/* Destination Segmented Control — Concise Labels that Never Truncate on Mobile */}
            <div className="grid grid-cols-3 gap-1.5 p-1 rounded-xl bg-slate-950 border border-slate-800/80">
              <button
                type="button"
                onClick={() => setExternalDestination('drive')}
                className={`py-2 px-2 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                  externalDestination === 'drive'
                    ? 'bg-emerald-600 text-white shadow-sm'
                    : 'text-slate-400 hover:text-slate-200'
                }`}
              >
                <HardDrive className="w-3.5 h-3.5 shrink-0" />
                <span>إلى Drive</span>
              </button>
              <button
                type="button"
                onClick={() => setExternalDestination('telegram')}
                className={`py-2 px-2 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                  externalDestination === 'telegram'
                    ? 'bg-sky-600 text-white shadow-sm'
                    : 'text-slate-400 hover:text-slate-200'
                }`}
              >
                <Smartphone className="w-3.5 h-3.5 shrink-0" />
                <span>إلى تليجرام</span>
              </button>
              <button
                type="button"
                onClick={() => setExternalDestination('device')}
                className={`py-2 px-2 rounded-lg text-xs font-semibold flex items-center justify-center gap-1.5 transition cursor-pointer whitespace-nowrap ${
                  externalDestination === 'device'
                    ? 'bg-indigo-600 text-white shadow-sm'
                    : 'text-slate-400 hover:text-slate-200'
                }`}
              >
                <Download className="w-3.5 h-3.5 shrink-0" />
                <span>لجهازي</span>
              </button>
            </div>

            {/* URL Input & Single Submit Button */}
            <div className="flex flex-col sm:flex-row gap-2.5">
              <input
                type="url"
                required
                dir="ltr"
                value={externalUrlInput}
                onChange={(e) => setExternalUrlInput(e.target.value)}
                placeholder="https://www.youtube.com/watch?v=... أو رابط TikTok / Drive / MediaFire..."
                className="flex-1 px-4 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-sm text-white placeholder-slate-500 focus:outline-none focus:border-sky-500"
              />
              <button
                type="submit"
                disabled={submittingUrl || !externalUrlInput.trim()}
                className="px-6 py-2.5 rounded-xl bg-sky-600 hover:bg-sky-500 text-white font-semibold text-sm transition flex items-center justify-center gap-2 shrink-0 cursor-pointer disabled:opacity-50 whitespace-nowrap"
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
                <span>بدء التنفيذ</span>
              </button>
            </div>
          </form>
        </section>

        {/* Core Card 2: Live Personal Transfer Queue & History */}
        <section className="bg-[#0D1322] border border-slate-800/90 rounded-2xl p-4 sm:p-6 space-y-4">
          <div className="flex flex-wrap items-center justify-between gap-3 border-b border-slate-800/80 pb-3.5">
            <div className="flex items-center gap-2">
              <Activity className="w-4 h-4 text-sky-400" />
              <h2 className="text-base font-bold text-white">العمليات الجارية وسجل النقل</h2>
            </div>

            <div className="flex items-center gap-2">
              {(serverStatus?.stats.activeJobs || 0) + (serverStatus?.stats.waitingAuthJobs || 0) > 0 && (
                <button
                  onClick={() => handleCancelAllJobs('personal')}
                  className="px-3 py-1.5 rounded-lg bg-rose-500/10 hover:bg-rose-500/20 border border-rose-500/30 text-rose-300 text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap"
                >
                  <Ban className="w-3.5 h-3.5" />
                  <span>إلغاء الجارية</span>
                </button>
              )}

              {(serverStatus?.stats.failedJobs || 0) > 0 && (
                <button
                  onClick={handleClearFailedJobs}
                  disabled={clearingFailed}
                  className="px-3 py-1.5 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-300 text-xs font-semibold flex items-center gap-1.5 transition cursor-pointer whitespace-nowrap"
                >
                  <Trash2 className="w-3.5 h-3.5 text-rose-400" />
                  <span>مسح الفاشلة ({serverStatus?.stats.failedJobs})</span>
                </button>
              )}
            </div>
          </div>

          {!serverStatus || serverStatus.jobs.length === 0 ? (
            <div className="py-10 text-center border border-dashed border-slate-800 rounded-xl space-y-1.5">
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
                        <span className="font-semibold text-sm text-white truncate max-w-xs sm:max-w-md" dir="auto">
                          {job.fileName}
                        </span>
                        <span className="text-xs text-slate-400">
                          · {job.direction === 'to_telegram' ? 'إلى تليجرام' : 'إلى Drive'}
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
                          <a
                            href={`/api/direct-download?jobId=${encodeURIComponent(job.id)}${
                              personalEmail ? `&userEmail=${encodeURIComponent(personalEmail)}` : ''
                            }${personalChatId ? `&chatId=${encodeURIComponent(personalChatId)}` : ''}`}
                            download
                            className="text-indigo-400 hover:text-indigo-300 font-semibold flex items-center gap-1"
                          >
                            <Download className="w-3.5 h-3.5" />
                            <span>تحميل</span>
                          </a>
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
                      <p className="text-xs text-rose-400 bg-rose-950/30 border border-rose-500/20 rounded-lg px-3 py-1.5">
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
          POPUP MODALS (جميع القوائم والخيارات مخفية في صفحات منبثقة)
         ===================================================================== */}
      {activeModal && (
        <div
          className="fixed inset-0 z-50 bg-black/75 backdrop-blur-sm flex items-center justify-center p-3 sm:p-6 overflow-y-auto"
          onClick={() => setActiveModal(null)}
        >
          <div
            className="bg-[#0D1322] border border-slate-800 rounded-2xl w-full max-w-3xl max-h-[88vh] flex flex-col shadow-2xl overflow-hidden"
            onClick={(e) => e.stopPropagation()}
          >
            {/* Modal Header */}
            <div className="px-5 py-4 border-b border-slate-800 flex items-center justify-between gap-3 shrink-0">
              <div className="flex items-center gap-2.5">
                {activeModal === 'drive_files' && <HardDrive className="w-5 h-5 text-sky-400" />}
                {activeModal === 'large_upload' && <UploadCloud className="w-5 h-5 text-indigo-400" />}
                {activeModal === 'settings' && <Settings className="w-5 h-5 text-emerald-400" />}
                {activeModal === 'admin' && <ShieldAlert className="w-5 h-5 text-amber-400" />}
                {activeModal === 'url_options' && <Sliders className="w-5 h-5 text-sky-400" />}
                <h2 className="text-base font-bold text-white">
                  {activeModal === 'drive_files' && 'ملفاتي ومجلداتي في Google Drive'}
                  {activeModal === 'large_upload' && 'رفع الملفات الضخمة مباشرة'}
                  {activeModal === 'settings' && 'حسابي الشخصي وإعدادات الربط'}
                  {activeModal === 'admin' && 'إدارة البوت وتشغيل Vercel'}
                  {activeModal === 'url_options' && 'خيارات الجودة والضغط للسحب'}
                </h2>
              </div>

              <button
                onClick={() => setActiveModal(null)}
                className="p-1.5 rounded-lg bg-slate-900 hover:bg-slate-800 text-slate-400 hover:text-white transition cursor-pointer"
                aria-label="إغلاق النافذة"
              >
                <X className="w-4 h-4" />
              </button>
            </div>

            {/* Modal Body */}
            <div className="p-5 overflow-y-auto space-y-5 flex-1">
              {/* MODAL 1: URL EXTRACTION OPTIONS */}
              {activeModal === 'url_options' && (
                <div className="space-y-4">
                  <div>
                    <label className="block text-xs font-semibold text-slate-300 mb-2">
                      صيغة الملف المسحوب
                    </label>
                    <div className="grid grid-cols-2 gap-2.5">
                      <button
                        type="button"
                        onClick={() => {
                          setExternalMediaFormat('video');
                          setExternalQuality('720');
                        }}
                        className={`py-2.5 px-3 rounded-xl text-xs font-semibold border transition cursor-pointer ${
                          externalMediaFormat === 'video'
                            ? 'bg-sky-500/20 border-sky-500/40 text-sky-300'
                            : 'bg-slate-900 border-slate-800 text-slate-400'
                        }`}
                      >
                        فيديو (MP4)
                      </button>
                      <button
                        type="button"
                        onClick={() => {
                          setExternalMediaFormat('audio');
                          setExternalQuality('320');
                        }}
                        className={`py-2.5 px-3 rounded-xl text-xs font-semibold border transition cursor-pointer ${
                          externalMediaFormat === 'audio'
                            ? 'bg-amber-500/20 border-amber-500/40 text-amber-300'
                            : 'bg-slate-900 border-slate-800 text-slate-400'
                        }`}
                      >
                        صوت فقط (MP3)
                      </button>
                    </div>
                  </div>

                  <div>
                    <label className="block text-xs font-semibold text-slate-300 mb-2">
                      {externalMediaFormat === 'audio' ? 'جودة الصوت (Bitrate)' : 'دقة الفيديو'}
                    </label>
                    {externalMediaFormat === 'video' ? (
                      <select
                        value={externalQuality}
                        onChange={(e) => setExternalQuality(e.target.value)}
                        className="w-full px-3.5 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                      >
                        <option value="1080">1080p Full HD (عالية جداً)</option>
                        <option value="720">720p HD (موصى بها وسريعة)</option>
                        <option value="480">480p (متوسطة لتوفير الحجم)</option>
                        <option value="360">360p (خفيفة وسريعة)</option>
                        <option value="240">240p (أقل استهلاك للبيانات)</option>
                      </select>
                    ) : (
                      <select
                        value={externalQuality}
                        onChange={(e) => setExternalQuality(e.target.value)}
                        className="w-full px-3.5 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                      >
                        <option value="320">320 kbps (نقاء فائق)</option>
                        <option value="192">192 kbps (جودة ممتازة)</option>
                        <option value="128">128 kbps (حجم خفيف)</option>
                      </select>
                    )}
                  </div>

                  <div>
                    <label className="block text-xs font-semibold text-slate-300 mb-2">
                      ضغط الملف قبل النقل أو التحميل
                    </label>
                    <select
                      value={externalCompressMode}
                      onChange={(e) => setExternalCompressMode(e.target.value as CompressMode)}
                      className="w-full px-3.5 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white"
                    >
                      <option value="none">بدون ضغط (الحجم الأصلي الكامل)</option>
                      <option value="zip">ضغط أرشيف ZIP (.zip)</option>
                      <option value="media">تقليص حجم الفيديو/الصوت (FFmpeg)</option>
                    </select>
                  </div>

                  <div>
                    <label className="block text-xs font-semibold text-slate-300 mb-2">
                      اسم مخصص للملف (اختياري)
                    </label>
                    <input
                      type="text"
                      value={externalCustomName}
                      onChange={(e) => setExternalCustomName(e.target.value)}
                      placeholder="اتركه فارغاً لاستخدام الاسم الأصلي"
                      className="w-full px-3.5 py-2.5 rounded-xl bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                    />
                  </div>

                  <div className="pt-2 flex justify-end">
                    <button
                      type="button"
                      onClick={() => setActiveModal(null)}
                      className="px-5 py-2 rounded-xl bg-sky-600 hover:bg-sky-500 text-white text-xs font-semibold cursor-pointer"
                    >
                      حفظ وإغلاق
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

                          <form onSubmit={handleCreateNewFolder} className="flex items-center gap-2">
                            <input
                              type="text"
                              value={newFolderInput}
                              onChange={(e) => setNewFolderInput(e.target.value)}
                              placeholder="اسم مجلد جديد..."
                              className="px-3 py-1.5 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                            />
                            <button
                              type="submit"
                              disabled={creatingFolder || !newFolderInput.trim()}
                              className="px-3 py-1.5 rounded-lg bg-emerald-600 hover:bg-emerald-500 disabled:opacity-50 text-white font-semibold text-xs flex items-center gap-1 cursor-pointer whitespace-nowrap"
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

                                  <a
                                    href={`/api/direct-download?driveFileId=${encodeURIComponent(file.id)}${
                                      personalEmail ? `&userEmail=${encodeURIComponent(personalEmail)}` : ''
                                    }${personalChatId ? `&chatId=${encodeURIComponent(personalChatId)}` : ''}`}
                                    download={file.name}
                                    className="px-2.5 py-1 rounded-lg bg-indigo-500/15 hover:bg-indigo-500/25 text-indigo-300 font-semibold flex items-center gap-1"
                                  >
                                    <Download className="w-3 h-3" />
                                    <span>تحميل</span>
                                  </a>

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
                    <label className="block border-2 border-dashed border-slate-700 hover:border-indigo-500/60 rounded-2xl p-10 text-center cursor-pointer transition bg-slate-900/40">
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
                    <div className="p-4 rounded-xl bg-amber-950/60 border border-amber-500/40 space-y-2.5 text-xs">
                      <p className="font-bold text-amber-200">
                        لتفعيل نافذة تسجيل الدخول بـ Google على دومين Vercel الجديد ({unauthorizedDomainHost}):
                      </p>
                      <p className="text-amber-100/90 leading-relaxed">
                        انسخ النطاق أدناه وأضفه في لوحة تحكم Firebase (Authentication → Settings → Authorized domains) ليعمل الدخول بضغطة زر على هذا النطاق:
                      </p>
                      <div className="flex items-center justify-between gap-2 p-2 rounded-lg bg-slate-950 border border-amber-500/30">
                        <code className="text-amber-300 font-mono" dir="ltr">
                          {unauthorizedDomainHost}
                        </code>
                        <button
                          onClick={() => {
                            navigator.clipboard.writeText(unauthorizedDomainHost);
                            setCopiedDomain(true);
                            setTimeout(() => setCopiedDomain(false), 2000);
                          }}
                          className="px-2.5 py-1 rounded bg-amber-500/20 hover:bg-amber-500/30 text-amber-200 font-semibold cursor-pointer"
                        >
                          {copiedDomain ? 'تم النسخ' : 'نسخ النطاق'}
                        </button>
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
                    <div className="flex flex-col sm:flex-row gap-2">
                      <input
                        type="text"
                        dir="ltr"
                        value={customClientId}
                        onChange={(e) => {
                          setCustomClientId(e.target.value);
                          localStorage.setItem(STORAGE_CUSTOM_CLIENT_ID_KEY, e.target.value.trim());
                        }}
                        placeholder="xxxx.apps.googleusercontent.com (اتركه فارغاً للافتراضي)"
                        className="flex-1 px-3 py-1.5 rounded-lg bg-slate-950 border border-slate-800 text-xs text-white placeholder-slate-500"
                      />
                    </div>
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
