# Generator game cloud module

The generator game and group Sudoku are peer applications. They share the existing CloudBase HTTP transport and signed login, but no progress collections or progress routes.

- Production collections: `generators_records`, `generators_requests`.
- Test collections: `generators_test_records`, `generators_test_requests`.
- All four collections use `ADMINONLY`: browser clients call the authenticated HTTP service, never the database directly.
- `GENERATORS_COLLECTION_PREFIX` can override the generator collection prefix. The existing test host selects `generators_test_`; production selects `generators_`.
- Existing `/api/login`, `/api/progress`, `/api/records`, roster and Sudoku collections remain unchanged.

Routes under the existing `/records` base:

- `GET /api/generators/progress`: signed player session, own verified journey and cumulative consumed lives.
- `POST /api/generators/attempts`: signed player session and UUID, group key, stage, seeds, preset and elapsed seconds. Server computes the generated subgroup and verifies the generating budget. Reusing a UUID with another payload/account fails; exact retries do not count a failure twice.
- `GET /api/generators/records`: public ranking with initials and masked student IDs; no raw account ID or proofs.
- `GET /api/generators/admin/records`: existing teacher token required; full records for export.

The browser keeps a per-account retry outbox. Cloud and local progress merge without lowering local progress. Historical local summaries lack generation proofs and are retained locally, not silently promoted to server-verified results. Replaying the relevant stages establishes verified cloud progress. Partial stage proofs may arrive out of order; only contiguous completed stages contribute to the ranking.

Tests: `node --test services/group-sudoku-records/cloudbase/service.test.mjs courses/abstract-algebra/generators/generator-sync.test.mjs`.

Deploy the shared host with dependencies included; preserve its environment variables, gateway paths and CORS configuration. Validate the test host first, retain a rollback version, and compare original Sudoku public records before/after the production update. Test writes belong only in test collections.

Verified deployment (2026-09-29): both production routes returned HTTP 200; the original Sudoku public-record digest was unchanged; GitHub Pages preflight returned 204 with the same allowed origin. Cloud function version `1` retains the pre-generator host as a rollback snapshot (0% traffic). Test smoke checks passed on the dedicated test collections.
