# Group Sudoku server records

The GitHub Pages site calls this API; the student roster and completion records are **not** static assets and must never be placed in the Pages repository. The server stores them in SQLite on a persistent private disk. The supplied workbook is read-only; only student ID and name are imported.

## Start on an existing server

Requires Node.js 24+. Copy this repository onto the application server. Run as a dedicated unprivileged service account; keep the data directory outside the web root. Provide these environment variables through the server's secret manager or a mode-0600 environment file, not through source control:

- `RECORDS_DB`: absolute path to a persistent private `records.sqlite` file.
- `RECORDS_ROSTER`: absolute path to the private JSON produced by the import script (omit after the first import if desired).
- `RECORDS_SECRET`: persistent random secret, at least 32 characters. Keep it stable across restarts; changing it invalidates lookup/admin tokens.
- `RECORDS_ADMIN_PASSWORD`: random teacher password, at least 16 characters.
- `RECORDS_ORIGINS`: comma-separated website origins, normally `https://birationalclass.github.io`.
- `HOST`: default `127.0.0.1` for a reverse proxy on the same machine.
- `PORT`: default `8782`.
- `RECORDS_TRUST_PROXY=1`: only for a reverse proxy on localhost that overwrites `X-Real-IP` with the actual client IP. Otherwise leave unset. Forwarded IPs are ignored from non-loopback peers.

Import locally or on the authorized server:

```sh
python3 -m pip install -r services/group-sudoku-records/requirements.txt
python3 services/group-sudoku-records/import-roster.py /private/path/roster.xlsx /private/data/roster.json
node services/group-sudoku-records/server.mjs
```

Expose only `/api/*` through an HTTPS reverse proxy, with request size limited to 16 KB. Do not expose SQLite, its WAL files, the roster JSON, environment files, or the source workbook. Back up SQLite using the SQLite backup API or stop/checkpoint the service before copying it. Persist the data directory across deployments; do not put it on an ephemeral container filesystem. For a local reverse proxy, enable `RECORDS_TRUST_PROXY=1` and set `X-Real-IP` to the real client IP so the classroom does not share one lookup quota. Also apply request limits at the proxy.

Set the public HTTPS API URL in `visuals/group-sudoku/records-config.mjs` only after provisioning and verifying the server. The localhost URL is for development only. An unconfigured public URL reports that registration is unavailable; it never pretends that browser storage is a server save.

## Behaviour

- Registration appears after all eight domains are completed. Closing the popup does not lose local gameplay; use **Records → Register completion** to try again.
- Full 11-digit student ID triggers an exact lookup. There is no public roster/list endpoint. Names are read-only and must match the server's roster on submission.
- Server validates all eight submitted multiplication tables, their clues, and the group conditions before saving. This verifies puzzle completion, not a student's real-world identity or independent work.
- Every student's row retains its first completion time and updates its latest submission time. Retry IDs are idempotent, including when the original response was lost.
- Completion records are publicly readable without login, per the course owner’s instruction. Only completed students appear; uppercase pinyin initials (张三 → ZS) and masked student IDs are shown. The browser always fetches the server records on opening and refreshes every 30 seconds while the list remains open.
- Initials are generated privately during roster import using pypinyin FIRST_LETTER, with common surname overrides. Unusual name readings can be corrected in the private JSON `initials` field. Re-import existing rosters to populate initials; unmigrated names are never returned by the public list. Lookup and teacher exports retain full names.
- Teacher access uses a separate password and an expiring token kept only in memory. The teacher can list all records and export CSV. The full roster is not public; only completion records are listed.
- On mobile, the ID input has `inputmode=numeric`, a fixed 11-digit constraint, and a keyboard-aware scrollable dialog. Focus is requested synchronously when the dialog opens; mobile OS policy may still require a tap.

## Verification

```sh
node --test services/group-sudoku-records/server.test.mjs visuals/group-sudoku/tests/*.test.*
```

Tests use fictional students and disposable databases, including persistence across server restart, server-side puzzle validation, retry deduplication, roster matching, public ID masking, teacher expiry and rate limits. Do not use real student records for a public preview.

Official references: [GitHub Pages is static hosting](https://docs.github.com/en/pages/getting-started-with-github-pages/what-is-github-pages), [Node SQLite API](https://nodejs.org/api/sqlite.html).

## Live free deployment

The production API uses the Workers + D1 implementation in [cloudflare/](cloudflare/README.md). Deployed 2026-09-21 on Workers Free, with a private APAC D1 database and 129 roster entries. See that directory for deployment and test details. The Node server above remains a self-hosting alternative.
