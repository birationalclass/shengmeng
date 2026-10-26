# Classroom delivery

Seven Algebra I courses share content-addressed glyph packs. Each course has a
compressed metadata pack, an independent opening pack, and groups of four boards.
Gzip envelopes contain the exact published SVG, JSON and MP3 bytes; speech and
timing are not regenerated. The first board gates startup. All other resources
continue loading in the background.

`course-pack-cache.js` verifies SHA256 and persists compressed responses in
Cache Storage (`refuge-course-packs-v1`). Decoded pack memory is bounded to 24 MiB
apart from a single larger active pack. The existing current/next PCM audio
transport remains in charge of playback. Content hashes isolate updates.

Concurrent readers share transfers. A cancelled reader is detached individually;
the final cancellation aborts the network transfer. Foreground requests promote
queued pack requests. Unsupported decompression and failed pack transfers fall
back to the original public files. Storage denial does not prevent playback.
The explicit save action checks that the index and every pack were persisted
before reporting success. Browsers may later evict stored site data.

The complete native offline distribution retains its original unpacked assets.
Its entry documents set `REFUGE_LOCAL`, so local delivery uses those files without
duplicating hundreds of megabytes of packed copies. The ZIP requires no external
runtime installation and no network for classroom playback.

After changing delivery modules, rebuild the main opening bundles and the
standalone Blackboard bundle. The unbundled 2D classroom module graph uses one
delivery version to prevent stale HTTP-cache imports from bypassing the store.
