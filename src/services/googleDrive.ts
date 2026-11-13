export interface DriveFolder {
  id: string;
  name: string;
}

export interface DriveFile {
  id: string;
  name: string;
  mimeType: string;
  size?: string;
  webViewLink?: string;
  createdTime?: string;
}

function notifyIfUnauthorized(status: number) {
  if (status === 401) {
    if (typeof window !== 'undefined') {
      window.dispatchEvent(new CustomEvent('tg-drive-token-expired'));
    }
    throw new Error('DRIVE_TOKEN_EXPIRED');
  }
}

export async function listFolders(accessToken: string): Promise<DriveFolder[]> {
  const q = encodeURIComponent("mimeType = 'application/vnd.google-apps.folder' and trashed = false");
  const url = `https://www.googleapis.com/drive/v3/files?q=${q}&fields=files(id,name)&orderBy=name&pageSize=100`;
  const res = await fetch(url, {
    headers: { Authorization: `Bearer ${accessToken}` },
  });
  notifyIfUnauthorized(res.status);
  if (!res.ok) {
    throw new Error('تعذر جلب المجلدات من Google Drive.');
  }
  const data = await res.json();
  return Array.isArray(data.files) ? data.files : [];
}

export async function createFolder(accessToken: string, name: string): Promise<DriveFolder> {
  const res = await fetch('https://www.googleapis.com/drive/v3/files?fields=id,name', {
    method: 'POST',
    headers: {
      Authorization: `Bearer ${accessToken}`,
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({
      name: name.trim(),
      mimeType: 'application/vnd.google-apps.folder',
    }),
  });
  notifyIfUnauthorized(res.status);
  if (!res.ok) {
    throw new Error('تعذر إنشاء المجلد الجديد في Google Drive.');
  }
  return await res.json();
}

export async function listFiles(accessToken: string): Promise<DriveFile[]> {
  const q = encodeURIComponent("mimeType != 'application/vnd.google-apps.folder' and trashed = false");
  const url = `https://www.googleapis.com/drive/v3/files?q=${q}&fields=files(id,name,mimeType,size,webViewLink,createdTime)&orderBy=createdTime desc&pageSize=100`;
  const res = await fetch(url, {
    headers: { Authorization: `Bearer ${accessToken}` },
  });
  notifyIfUnauthorized(res.status);
  if (!res.ok) {
    throw new Error('تعذر جلب الملفات من Google Drive.');
  }
  const data = await res.json();
  return Array.isArray(data.files) ? data.files : [];
}

export async function deleteFile(accessToken: string, fileId: string): Promise<void> {
  const res = await fetch(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(fileId)}`, {
    method: 'DELETE',
    headers: { Authorization: `Bearer ${accessToken}` },
  });
  notifyIfUnauthorized(res.status);
  if (!res.ok && res.status !== 204) {
    throw new Error('تعذر حذف الملف من Google Drive.');
  }
}

export async function startResumableUpload(
  accessToken: string,
  file: File,
  parentFolderId?: string
): Promise<string> {
  const metadata: Record<string, any> = {
    name: file.name,
  };
  if (parentFolderId) {
    metadata.parents = [parentFolderId];
  }

  const res = await fetch(
    'https://www.googleapis.com/upload/drive/v3/files?uploadType=resumable&fields=id,name,webViewLink',
    {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${accessToken}`,
        'Content-Type': 'application/json; charset=UTF-8',
        'X-Upload-Content-Type': file.type || 'application/octet-stream',
        'X-Upload-Content-Length': String(file.size),
      },
      body: JSON.stringify(metadata),
    }
  );

  notifyIfUnauthorized(res.status);
  if (!res.ok) {
    throw new Error('تعذر بدء جلسة الرفع القابل للاستئناف في Google Drive.');
  }

  const sessionUri = res.headers.get('location') || res.headers.get('Location');
  if (!sessionUri) {
    throw new Error('لم يُرجع Google Drive رابط جلسة الرفع.');
  }
  return sessionUri;
}

export async function uploadChunk(
  sessionUri: string,
  chunk: Blob,
  offset: number,
  totalSize: number
): Promise<{ done: boolean; data?: any }> {
  const endByte = offset + chunk.size - 1;
  const res = await fetch(sessionUri, {
    method: 'PUT',
    headers: {
      'Content-Range': `bytes ${offset}-${endByte}/${totalSize}`,
    },
    body: chunk,
  });

  if (res.status === 308) {
    return { done: false };
  }

  notifyIfUnauthorized(res.status);
  if (res.ok) {
    const data = await res.json().catch(() => ({}));
    return { done: true, data };
  }

  throw new Error(`فشل رفع الجزء إلى Google Drive (رمز الحالة ${res.status}).`);
}
