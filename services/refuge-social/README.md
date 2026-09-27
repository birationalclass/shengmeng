# Refuge social service

Independent CloudBase collections in the existing Shanghai environment. The Sudoku collections and functions are not used or modified.

## Deployment

Use the official authenticated CloudBase CLI from this directory:

```sh
tcb fn deploy refuge-social --config-file /path/to/private-production-ai.json --runtime Nodejs20.19 --install-dependency true --force --json
```

Production HTTP mapping: `/refuge` -> `refuge-social`. Staging: `/refuge-test` -> `refuge-social-test`, with `REFUGE_PREFIX=refuge_test_`. Staging and production use distinct session cookies. The static frontend defaults to production; on localhost only, `?social=test` selects staging and `?social=local` selects the development API.

Collections: `refuge_users`, `refuge_sessions`, `refuge_messages`, `refuge_limits`; test equivalents use `refuge_test_`. All have ADMINONLY client access. The function accesses them server-side. Messages are retained; the client reads the latest 50. Create an ascending `createdAt` index on messages, and TTL indexes with `expireAfterSeconds: 0` on sessions `expiresOn` and limits `expiresAt`.

## Accounts and moderation

Public registration always creates members, never administrators. Passwords use random salt + scrypt. Session tokens are random and stored only as hashes; browser cookies are HttpOnly, Secure, SameSite=None, Partitioned. Remembered sessions last 30 days. JSON POST requests require an explicitly allowed Origin. Rate limits apply to login, signup, reads, writes and administration. The existing requested administrator is provisioned directly in production; no plaintext password or bootstrap backdoor is included in the repository.

The administrator can page through accounts with their most recent successful login time and apply or remove a 1-hour, 1-day or 7-day mute. Every administrative request rechecks the server-side role; every message rechecks the mute deadline. No IP addresses or passwords are shown in the account list. Account recovery and password reset are not implemented.

Chat polls every 5 seconds when expanded, 60 seconds when collapsed, and stops when hidden, before entry, or after 2 minutes without interaction. Expired session/limit records are removed by TTL; chat is not automatically deleted. The free resource-point pool is shared with the other services in this environment.

## Verification

```sh
node --test service.test.mjs
node local.mjs
```

Local API uses in-memory SQLite unless `REFUGE_DB` names a persistent SQLite file. Do not expose the local development server publicly. Browser QA should use the isolated staging route. Never commit live credentials, session tokens or database exports.


## Private scene AI

The AI button sends only a JPEG of the 3D canvas, never account/chat UI. Public messages and private AI jobs are separate. Every history/poll request is scoped to the authenticated user. Screenshots are passed to the selected provider and are not retained in CloudBase; questions and answers are retained in `refuge_ai_jobs` (latest 20 displayed). Provider retention policies still apply.

Create ADMINONLY `refuge_settings` and `refuge_ai_jobs`, with a `{userId:1,createdAt:-1}` index on the latter. Set a stable random `REFUGE_AI_SECRET` (at least 32 characters) in the function environment. Keep it outside Git and preserve it across deployments: changing it makes saved API keys unreadable. This workstation's private deployment config is `.tools/refuge-cloudbase/production-ai.json` outside the release checkout. Deploy from this service directory; its `functionRoot` is `..`. Function timeout is 60 seconds.

An administrator opens chat → ⋯ to configure the model and API Key. Credentials are AES-256-GCM encrypted server-side and never returned to the client. Saving confirms storage, not provider validity. OpenAI Responses and Qwen vision (Beijing endpoint) are supported. Users select their provider locally. AI API billing is separate from CloudBase quota. Limits: 3 starts/minute and 20/day per account, 100/day total. Ordinary Enter sends public chat; the AI button explicitly sends a private visual question. Unconfigured providers return a clear error without fabricating an answer.

The panel supports safe text, bold, inline code and local KaTeX formulas. HTML is never interpreted. Window position, dimensions and selected provider are stored in the browser, not the account. Resize minimum is 280×180, maximum width is 50% of the viewport and maximum height is 480px. Viewport limits override the minimum on small screens.

Tests: `node --test service.test.mjs ai.test.mjs ../../visuals/math-refuge/social-send.test.mjs`.
