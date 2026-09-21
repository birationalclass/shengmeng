# Shanghai CloudBase records backend

The GitHub Pages game calls a standard HTTPS cloud-function endpoint. Its private roster and completion records live in the Shanghai CloudBase document database. The browser needs no Tencent account and no additional SDK.

## Current setup

- Region: `ap-shanghai`; environment `birationalclass-d3fw2j6t76955af0`.
- Function: `group-sudoku-records`, event type, `Nodejs20.19`, `index.main`, 256 MB, 15 seconds.
- API base: `https://birationalclass-d3fw2j6t76955af0-1493130792.ap-shanghai.app.tcloudbase.com/records`.
- HTTP gateway maps `/records` to the event function. The handler implements its own exact-origin CORS allowlist, including preflight. Teacher access remains password/token protected.
- `sudoku_students`, `sudoku_completions`, `sudoku_requests`, `sudoku_limits` all have `ADMINONLY` database permissions. There is no direct public database access. A TTL index removes expired rate-limit entries.
- Separate `sudoku_test_` collections and `group-sudoku-records-test` contain only fictional students.
- Experience plan expires 2027-03-21; automatic renewal and paid overage are off. Check quota and renew manually before expiry. This is not permanent unlimited hosting.

The free environment rejects adding Web SDK security domains (`OperationDenied.FreePackageDenied`), so the published integration uses the supported HTTP-function API. Default-domain browser navigation can show an interstitial or download; API fetch requests return JSON. Production custom domains are recommended by Tencent, but not provisioned here. Do not treat a successful test on one network as a guarantee for every mainland ISP.

## Deployment

Bundle `index.mjs` as CommonJS `index.js` with esbuild for Node 20; keep `@cloudbase/node-sdk` external and declare exact version `3.18.3` in the function's private package.json. CloudBase installs this dependency during deployment.

Set `RECORDS_SECRET` (at least 32 characters), `RECORDS_ADMIN_PASSWORD` (at least 8), and `RECORDS_COLLECTION_PREFIX` (`sudoku_` for production). `RECORDS_ORIGINS` defaults to `https://birationalclass.github.io`; localhost is permitted only in the testing function. Keep credentials, roster and database exports outside source control.

Create collections with `PermissionInfo.AclTag=ADMINONLY` and verify their ACLs before importing. Students use document ID = full student ID and fields `{id,name,initials}`. Student progress uses document ID = full ID; guests use a generated `guest_` UUID. Records contain `{id,kind,name,initials,completedLevels,boards,first_at,reached_at,updated_at}`. Progress writes and retry IDs are committed in a transaction. A new higher level changes `reached_at`; retries and replaying equal/lower levels preserve it. Legacy eight-level records keep their timestamps and restore boards from the previous request log when necessary.

Configure the event function's HTTP path using CloudBase's `CreateCloudBaseGWAPI` (`ServiceId`, `Path`, `Type:1`, `Name`, `AuthSwitch:2`, `EnableUnion:true`). The service's exact-origin CORS and teacher authentication apply independently of this public route. New route CLI commands for custom domains reject platform-owned default domains; use the event-function access API for this integration.

## Cutover and backups

The previous Cloudflare Worker rejects new completion submissions with a refresh message (`RECORDS_READ_ONLY=true`). Its original D1 database is retained. A private SQL backup was taken after writes were frozen; it contained 129 roster entries and zero completion/request rows. The roster was imported into CloudBase and the count verified. Never add these private backups to the Pages repository.

For future migrations, freeze old writes, back up, import without changing original timestamps, verify the new service and only then switch the frontend configuration. The Node SQLite and Cloudflare implementations remain alternatives.

## Verification

`node --test services/group-sudoku-records/cloudbase/service.test.mjs visuals/group-sudoku/tests/records-api.test.mjs`

Local tests check transactions, retries, pagination, privacy, teacher access, origins and network error handling. Remote smoke tests use fictional students and check valid completion, rejected incomplete boards, duplicate retries, public initials and teacher export. Production checks read the real roster without writing fake completion records. Browser QA checks saved receipts and the public list at mobile width.

Official references: [HTTP functions](https://docs.cloudbase.net/service/access-cloud-function), [default-domain behavior](https://docs.cloudbase.net/service/alias), [CORS handling](https://docs.cloudbase.net/service/cors), [free plan](https://cloudbase.net/pricing).

## Player login and progress

`POST /api/lookup` returns the student name and a short-lived lookup token. `POST /api/login` accepts student ID plus this token, or guest mode (optionally an existing guest session). It returns a signed 30-day player session and saved boards. This is roster identification, not password-protected identity verification. A guest keeps the same identity on the same browser while its session remains valid.

`POST /api/progress` requires a player bearer token and a unique submission ID. Only contiguous, clue-preserving valid group tables from 2×2 through the highest completed level are accepted. Each player's highest completion is retained. Public and teacher lists sort by completed-level count descending, then the first timestamp of reaching that count ascending. Public student names use initials; guests get a Guest prefix and no student ID.

Browser QA uses the separate testing function and fictional roster. The login input uses synchronous focus on user activation, numeric input mode, and visual-viewport sizing; actual software keyboard behavior depends on the mobile browser.
