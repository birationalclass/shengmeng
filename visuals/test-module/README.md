# 测试模块 · The Grammar of Becoming

An original 208-second real-time 3D overture about operations and human ideas.

## Story and visual direction

A brass mechanism carries the viewer over one pale, layered relief map above blue-grey water. Six architectural dioramas rise in chronological order: writing, a traditional Chinese timber tower, Newton’s manor, Galois’s French Gothic cathedral, an iron crystal hall, and an AI computation city. Five working timber drawbridges connect them. The river crossing is followed by a low bridge-level camera passage. The camera connects them spatially; the same material palette connects them visually. Names are engraved on physical landmark plaques, with explanatory text hidden by default.

- **Semigroup / 半群** (12–40 s): concatenate formal strings in an early archive.
- **Chinese Remainder Theorem / 中国剩余定理** (40–70 s): timber columns, bracket sets, balustrades and curved tile roofs assemble floor by floor. The 1247 Qin Jiushao scene includes a constructive CRT proof and the 23 modulo 105 example.
- **Action / 作用** (70–100 s): Newton’s English manor and ideal gravity flow; the apple falls at 85–89 s. Collision is excluded from the reversible mathematical model.
- **Permutation / 置换** (100–130 s): Galois, a French Gothic cathedral and three roots performing a cycle and transposition. The notes prove Gal(x³−2/ℚ) ≅ S₃.
- **Symmetry / 对称** (130–160 s): an industrial iron hall around a finite cubic lattice, with proofs for translations and a quarter-turn. The full classification of 230 space-group types is historical context, not claimed as proved here.
- **Composition / 复合** (160–192 s): glowing computations travel through a layered instrument among modern towers.
- The prologue orbits a brass armillary sphere; the coda (192–208 s) lifts above the six connected eras.

Camera positions and targets use time-scaled cubic Hermite curves, maintaining velocity through intermediate shot anchors. Centers are aligned with the architecture, with oblique close views, short lateral sweeps, low bridge passages, and a final crane out. Portrait devices receive a wider view. Captions and the progress slider are disabled by default and can be enabled in settings. After 208 seconds, the camera smoothly continues a panoramic tour while mechanisms keep moving; a softly pulsing bottom-center replay button restarts the sequence.

The user-provided [reference video](https://www.bilibili.com/video/BV1MFtC6gEhY/) informed the brass rings, pale relief map, miniature mechanisms, rising scenery and cinematic traversal. Only the accessible preview was available; the paid portion was not accessed, so this is not claimed to be a shot-for-shot reconstruction of the entire film. No footage, music, branding or extracted assets from that video or the television series are used. Models, map and label textures are generated locally by `scene.mjs`; `cover.svg` is an original vector illustration. Three.js and typefaces reuse this repository's existing licensed assets. Historical source links and short mathematical derivations appear in the page's “数学注脚”.

## Controls

Space: play/pause. Left/right: seek five seconds. 1–6: chapter. Drag: orbit around the current scene; wheel: zoom. Return-camera button restores the narrative route. Settings control speed, quality, captions, progress slider, dust, repeat and reduced motion. Opening settings does not stop the film. There are no video embeds, telemetry, AI API calls or external runtime requests. Music support accepts a local browser-playable file, with volume control and default playback; browsers that block autoplay start the music on the next page click or keypress. `soundtrack.mjs` points to the MP3 recorded from the user-selected QQ Music playback (application audio only, no microphone). The source recording is trimmed to one complete playthrough; music loops independently of the cinematic timeline. `?mute=1` enforces muted browser QA and prevents audio playback.

The loading screen waits for a deliberate “点击进入动画” click after the scene is ready. This gesture starts the timeline and default soundtrack together. Before entry, no animation or audio plays. Reduced motion can be selected in settings. WebGL failure retains an illustrated fallback and access to all mathematical notes. A single deterministic timeline drives cameras and models, so seeking is reversible. Settings are stored under `operations-atlas-v2`.

## Development and verification

Serve the repository root with `python3 -m http.server 8766` and open `/visuals/test-module/`.

Run `node --test visuals/test-module/story.test.mjs`. These tests check timeline boundaries, portrait/landscape camera position and velocity continuity, exhaustive CRT reconstruction for all 105 residue triples, the gravity-flow action law including inverse time, and the order and associativity of composition. The in-page algebraic arguments are proofs; finite automated examples are regression checks, not replacements for proofs.

Browser checks cover loading removal, all chapter boundaries, pause and seek, settings while playing, notes, manual camera and reset, quality, end-of-film and repeat behavior, enforced muted audio, and responsive layouts. UI controls use native buttons, range inputs and dialogs. Fullscreen exit does not navigate.
