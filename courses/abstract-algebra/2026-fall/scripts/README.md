# Lesson payloads

Edit the authoring files in `lesson-groups` (`content.js`, `chapter-two.js`, `exercises.js`, `textbook-references.js`; for rings, `chapter-three.js`, `chapter-four.js`, `ring-exercises.js`) or `lesson-1` (`notebook-content.js`, `exercises.js`). Then run from the semester directory:

```sh
node scripts/build-lesson-data.cjs
node tests/lesson-data.test.cjs
```

Commit the generated `sections/*.json`, `group-sections.js` and `lesson-1/exercises-runtime.js` alongside source changes. The site fetches exactly one section payload. Only the applicable group or ring model/rendering scripts load. Shared renderers start after that payload and the common dependencies are ready. The requested hash is used for the first displayed topic.

The portal removes the old iframe on exit or section changes. Browser destruction of that browsing context cancels requests and disposes its listeners, animation frames, timers and canvases; garbage collection determines when physical memory returns. Same-section topic navigation retains the current context. HTTP caching of downloaded files remains enabled.

Heavy opening scripts load only for the opening, including replay from a course reached via a lesson URL. Direct lesson URLs do not fetch the opening bundle.

Browser regression (requires Playwright and Chrome, plus a local HTTP server):

```sh
COURSE_TEST_URL=http://127.0.0.1:8768/courses/abstract-algebra/2026-fall/ node tests/lesson-loading.browser.cjs
```

Chapter 3–4 checks:

```sh
node tests/rings.test.cjs
COURSE_TEST_URL=http://127.0.0.1:8768/courses/abstract-algebra/2026-fall/ node tests/rings.browser.cjs
```

The model tests check integer arithmetic invariants, polynomial division,
Gaussian remainders, finite ring homomorphisms, content multiplicativity,
all numbered definition/theorem references, bilingual content and KaTeX.
The browser test covers all 84 cards in two languages and two viewport widths,
controls, proofs, all 55 exercises, current-section network requests and iframe
disposal. These are implementation checks; the proofs themselves are authored
and reviewed against the textbook, not formally verified by these tests.
