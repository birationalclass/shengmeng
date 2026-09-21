# Free Cloudflare deployment

This is the Workers + D1 alternative to the Node server. The public API contract is the same. Use the existing GitHub Pages website; deploy only the records API here. The full roster goes into private D1 tables, never GitHub or Worker source.

Keep the account on **Workers Free**. No paid upgrade or payment method is required for this architecture. As checked on 2026-09-21, the published free limits are 100,000 Worker requests/day and D1 5 million rows read/day, 100,000 rows written/day, 5 GB total storage. Exceeding free limits rejects operations until reset; it does not authorize upgrading the account. Monitor actual usage, including public refreshes and indexed writes.

Sources: [Workers pricing](https://developers.cloudflare.com/workers/platform/pricing/), [D1 pricing](https://developers.cloudflare.com/d1/platform/pricing/), [D1 batches and transactions](https://developers.cloudflare.com/d1/worker-api/d1-database/).

## Deployment

1. Sign into the owner's Cloudflare account and confirm it is on Workers Free. Run `wrangler login` to authorize the deployment CLI. Do not expose OAuth tokens in chat or source control.
2. From this directory run `wrangler d1 create shengmeng-group-sudoku-records`. Copy `wrangler.example.toml` to private/ignored `wrangler.toml`, with the returned database ID.
3. Run `wrangler d1 execute shengmeng-group-sudoku-records --remote --file schema.sql`.
4. Convert the previously imported private roster with `python3 roster-to-sql.py /private/path/roster.json /private/path/roster.sql`. Then run `wrangler d1 execute shengmeng-group-sudoku-records --remote --file /private/path/roster.sql`. Never print or commit its contents. This step transfers the roster to the owner's Cloudflare account.
5. Set `RECORDS_SECRET` and `RECORDS_ADMIN_PASSWORD` using `wrangler secret put` and private input. Use a persistent random signing secret of at least 32 characters and a teacher password of at least 8 characters. Securely provide the password to the teacher; never embed it in the webpage.
6. Run `wrangler deploy`. Check `/api/health`, anonymous `/api/records`, and CORS from the Pages origin.
7. For end-to-end submission tests, first deploy a **separate staging Worker + D1 database** using fictional students. Keep test submissions out of the real class table. Verify ID lookup, all-board validation, idempotent retries, masking, authenticated exports, and persistence across a second deployment.
8. Only after health and staging tests pass, set `RECORDS_API_URL` in the website to the verified production HTTPS URL, commit, push, and verify the actual page. An unconfigured or failing API is not a successful deployment.

## Local checks

Run `node --test worker.test.mjs` for SQLite-backed API checks. Run `wrangler dev --local` against a local D1 instance for workerd runtime verification. A generated `clues.mjs` avoids running the expensive puzzle generator inside the free CPU budget. Rebuild it with `node build-clues.mjs` whenever the public game clues change; tests compare all clues with the game source.

An atomic SQLite trigger updates the completion record only when a new request ID is inserted. Retries cannot alter the original timestamp. Sensitive endpoint rate limits persist in D1; daily cron removes expired rate-limit keys. Public list responses contain only initials, masked IDs, and times. Lookup and authenticated teacher export retain full names as requested.

## Deployment verified 2026-09-21

- Production: `https://shengmeng-group-sudoku-records.group-sudoku-cloudflare-staging.workers.dev`
- Database: `shengmeng-group-sudoku-records` (APAC); complete roster stored privately.
- Separate test Worker/database: `shengmeng-group-sudoku-test`; fictional students only.
- Workers plan confirmed in dashboard: **Free, $0**. No paid upgrade enabled.
- 49 local tests passed; the actual workerd local runtime and remote D1 submission/lookup/teacher authorization passed. A remote redeployment preserved the same completion record and timestamps. Production health, exact private roster lookup, Pages CORS, and teacher login passed; no fictional completion was inserted in production.
