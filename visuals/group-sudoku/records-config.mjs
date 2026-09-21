// Public API URL only. Credentials and the roster remain in private Cloudflare storage.
export const RECORDS_API_URL=['localhost','127.0.0.1'].includes(location.hostname)?'http://127.0.0.1:8782':'https://shengmeng-group-sudoku-records.group-sudoku-cloudflare-staging.workers.dev';
