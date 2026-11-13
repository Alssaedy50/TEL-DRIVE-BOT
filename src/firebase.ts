import { initializeApp } from 'firebase/app';
import {
  getAuth,
  signInWithPopup,
  signInWithRedirect,
  getRedirectResult,
  GoogleAuthProvider,
  onAuthStateChanged,
  User,
} from 'firebase/auth';
import firebaseConfig from '../firebase-applet-config.json';

const app = initializeApp(firebaseConfig);
export const auth = getAuth(app);

export const SCOPES = [
  'https://www.googleapis.com/auth/drive.file',
  'https://www.googleapis.com/auth/userinfo.email',
  'https://www.googleapis.com/auth/userinfo.profile',
];

const TOKEN_STORAGE_KEY = 'tg_drive_oauth_token';
const TOKEN_EXPIRY_KEY = 'tg_drive_oauth_expiry';
const TOKEN_TTL_MS = 50 * 60 * 1000; // 50 minutes

const provider = new GoogleAuthProvider();
for (const scope of SCOPES) {
  provider.addScope(scope);
}
provider.setCustomParameters({
  prompt: 'select_account',
  access_type: 'offline',
});

let isSigningIn = false;
let cachedAccessToken: string | null = loadStoredToken();

export function loadStoredToken(): string | null {
  try {
    const token = localStorage.getItem(TOKEN_STORAGE_KEY);
    const expiry = Number(localStorage.getItem(TOKEN_EXPIRY_KEY) || '0');
    if (token && expiry > Date.now()) {
      return token;
    }
    localStorage.removeItem(TOKEN_STORAGE_KEY);
    localStorage.removeItem(TOKEN_EXPIRY_KEY);
  } catch {
    // Ignore storage errors
  }
  return null;
}

export function getStoredTokenExpiry(): number {
  try {
    return Number(localStorage.getItem(TOKEN_EXPIRY_KEY) || '0');
  } catch {
    return 0;
  }
}

export function saveStoredToken(token: string, customExpiresAtMs?: number) {
  cachedAccessToken = token;
  try {
    const exp =
      customExpiresAtMs && customExpiresAtMs > Date.now()
        ? customExpiresAtMs
        : Date.now() + TOKEN_TTL_MS;
    localStorage.setItem(TOKEN_STORAGE_KEY, token);
    localStorage.setItem(TOKEN_EXPIRY_KEY, String(exp));
  } catch {
    // Ignore storage errors
  }
}

export function clearStoredToken() {
  cachedAccessToken = null;
  try {
    localStorage.removeItem(TOKEN_STORAGE_KEY);
    localStorage.removeItem(TOKEN_EXPIRY_KEY);
  } catch {
    // Ignore
  }
}

export const initAuth = (
  onAuthSuccess?: (user: User, token: string) => void,
  onAuthFailure?: () => void
) => {
  // Check if returning from a mobile redirect sign-in
  getRedirectResult(auth)
    .then((result) => {
      if (result) {
        const credential = GoogleAuthProvider.credentialFromResult(result);
        if (credential?.accessToken) {
          saveStoredToken(credential.accessToken);
          if (onAuthSuccess) onAuthSuccess(result.user, credential.accessToken);
        }
      }
    })
    .catch(() => {});

  return onAuthStateChanged(auth, async (user: User | null) => {
    const activeToken = cachedAccessToken || loadStoredToken();
    if (user && activeToken) {
      cachedAccessToken = activeToken;
      if (onAuthSuccess) onAuthSuccess(user, activeToken);
    } else if (!isSigningIn) {
      if (onAuthFailure) onAuthFailure();
    }
  });
};

export const googleSignIn = async (): Promise<{ user: User; accessToken: string } | null> => {
  try {
    isSigningIn = true;
    const result = await signInWithPopup(auth, provider);
    const credential = GoogleAuthProvider.credentialFromResult(result);
    if (!credential?.accessToken) {
      throw new Error('تعذر الحصول على رمز الوصول (Access Token) من حساب Google.');
    }

    saveStoredToken(credential.accessToken);
    return { user: result.user, accessToken: credential.accessToken };
  } catch (error: any) {
    if (error?.code === 'auth/popup-blocked') {
      await signInWithRedirect(auth, provider);
      return null;
    }
    console.error('Sign in error:', error);
    throw error;
  } finally {
    isSigningIn = false;
  }
};

export const getAccessToken = async (): Promise<string | null> => {
  return cachedAccessToken || loadStoredToken();
};

export const logout = async () => {
  clearStoredToken();
  await auth.signOut();
};
