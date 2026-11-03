import app from '../server.ts';

export const config = {
  maxDuration: 60,
};

export default function handler(req: any, res: any) {
  // Restore original path if rewritten by Vercel
  const matchedPath =
    (req.headers && (req.headers['x-matched-path'] as string)) ||
    (req.headers && (req.headers['x-forwarded-uri'] as string));

  if (matchedPath && matchedPath.startsWith('/api') && req.url !== matchedPath) {
    req.url = matchedPath;
  }

  return app(req, res);
}

