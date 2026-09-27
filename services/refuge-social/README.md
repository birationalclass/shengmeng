# Refuge social service

Independent CloudBase collections in the existing Shanghai environment. The Sudoku collections and functions are not used or modified.

## Deployment

Use the official authenticated CloudBase CLI from this directory:

```sh
tcb fn deploy refuge-social --runtime Nodejs20.19 --install-dependency true --force --json
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
