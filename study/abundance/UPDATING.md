# Abundance journal updates

The published journal is `study/abundance/index.html`. Its source data is `records.json`; presentation lives in `template.html`, `journal.css`, and `journal.js`.

For a new discussion, correct obvious speech-recognition errors and remove conversational repetition. Retain the mathematical question, assumptions, actual reasoning, conclusions, unresolved points, and the discussion time (with an explicit timezone). Do not invent a derivation, silently resolve an ambiguity, or treat a paper's assertion as a verified theorem. Preserve corrections explicitly. Do not publish account details, local paths, conversation identifiers, private third-party discussions, or operational chatter.

Append a record with a stable, unique ID. `status` is `open`, `checked`, or `corrected`; it describes the note. `proofStatus` is `unverified` or `verified`; `verified` requires concrete entries in `verification` identifying what was checked and its evidence. `conclusions` may include reading progress, which does not imply a verified mathematical proof. Empty fields stay empty and are not displayed. `materials` contains catalogue IDs only. Re-read existing records to avoid duplicating a discussion; unchanged content should produce no commit. Keep the original discussion time when refining an existing record, and update `updatedAt` only for a substantive change.

Run `node study/abundance/build.mjs` from the repository root after changing the JSON. This validates the data and regenerates static HTML, so records remain readable without JavaScript. Review the content and diff, publish only the changed journal files against the latest main branch, then verify GitHub Pages deployment. When another update races, re-read the latest record data before retrying; never force-push.

The source conversation coordinates approximately 30-minute updates when new learning content exists. This page does not poll private conversations, require credentials, or create a second scheduler.

Display questions and replies as separate dialogue messages. Preserve sourceTheorem.text exactly from the requested source theorem (including math notation); never replace it with a paraphrase. Formula delimiters $...$, \[...\], and \(...\) render with the shared KaTeX assets. Source proof status remains explicit.
