# Password-protected lesson and teaching plan

`index.html` is the public password form. `access.js` derives an AES-256-GCM key with PBKDF2-SHA256 and decrypts `lesson.enc.json` only after a correct password. The lesson HTML and its teaching JavaScript are encrypted together. The `teaching-plan/` directory uses the same format with a separate password. Passwords and decrypted pages are not saved in browser storage; reloading requires unlocking again.

Payload format: version 1; 310000 PBKDF2 iterations; base64 salt (16 bytes), IV (12 bytes), and ciphertext followed by the 16-byte GCM authentication tag. Plaintext is a complete UTF-8 HTML document. The original lesson math and interaction scripts run in order at the end of its decrypted body; relative stylesheet and navigation URLs are resolved against the unchanged page URL.

When editing these pages, decrypt a working copy outside the published repository, update it, and encrypt it again with a fresh random salt and IV. Preserve both password gates. Do not publish a plaintext HTML or JavaScript backup, password, or derived key. Update the asset version when replacing files. Historical public commits are not removed by this change.
