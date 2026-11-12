import app from '../server.ts';

export const config = {
  maxDuration: 60,
};

export default function handler(req: any, res: any) {
  // Restore original path if rewritten to /api/index while strictly preserving query string
  if (req.url && (req.url === '/api/index' || req.url.startsWith('/api/index?'))) {
    const matchedPath =
      (req.headers && (req.headers['x-matched-path'] as string)) ||
      (req.headers && (req.headers['x-forwarded-uri'] as string));

    if (matchedPath && matchedPath.startsWith('/api') && !matchedPath.startsWith('/api/index')) {
      const qIdx = req.url.indexOf('?');
      const query = qIdx >= 0 ? req.url.slice(qIdx) : '';
      req.url = matchedPath.split('?')[0] + query;
    }
  }

  return app(req, res);
}
