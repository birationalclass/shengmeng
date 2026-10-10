# Nef abundance learning conversation

Public page: study/abundance/index.html. Data: records.json (schemaVersion 2). Build with node study/abundance/build.mjs. Styling reuses visuals/catalog.css; journal.css adds only the reading and conversation layout.

Only publish mathematical technical discussion, original theorem material, notation clarifications and corrections. Exclude all website design, layout, colors, publishing, automation, screenshot instructions, navigation requests, tool operations, and status messages. Do not publish private paths, conversation IDs, account details or private third-party discussions. Correct speech recognition with context, remove repetitions, but preserve every substantive mathematical question, answer and correction. Never invent a derivation or treat a paper claim as verified.

Each record is one message with a unique stable id, role (user/assistant), original discussion time with timezone, zh/en arrays of paragraphs, and proofStatus. Translate faithfully; preserve hypotheses, formulas and uncertainty. Verified claims require verification evidence. Keep old messages in chronological order. Check source dialogue and existing records for duplicates before appending; no substantive new discussion means no commit. The source conversation handles the approximately 30-minute schedule; do not create another scheduler.

Keep the page minimal: Nef abundance title, official OpenAI paper link, a high-resolution crop from the original PDF (not an AI-generated theorem image or full-page PDF), then the technical conversation. Do not add slogans, question prompts, catalogues, counters, filters, workflow explanations or repeated caveats. The theorem's original English remains unchanged in both languages; its text is included only for accessibility. Use the current Visual gallery's light palette and typography. The page opens at the latest message after images/fonts load; language changes preserve the visible message and reading offset.

Preserve sourceTheorem.text exactly, and link sourceTheorem.url to the exact official paper. theorem-main.png is cropped from page 1 of the original PDF, rendered at 4000 pixels page height, crop pixels (370,2728,2460,3080). Inspect all edges and formulas after recropping. Source proof status stays unverified until actual checking.

Before publishing: build, validate both language versions, inspect the theorem crop and formula rendering, test latest-message positioning and language changes, compare modified files against current main, commit without force-pushing, then verify Pages and the real URL.

For contradictory or repetitive speech, keep the final clarified technical intent rather than every false start. In particular, the current request is to follow the original general proof in the K3 case; it is not a ban on Riemann–Roch. Do not replace this with an independent classical proof. Moving-jets/Frobenius steps remain unverified until the source discussion actually checks them.
