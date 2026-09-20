# 测试模块 · The Grammar of Becoming

An original silent, 114-second real-time 3D overture about operations and human ideas.

## Story and visual direction

A brass mechanism carries the viewer over one dark-green engraved map. Three clockwork dioramas rise in chronological order: Chinese characters and Latin letters, Newton's apple tree, and a layered computational instrument. The camera connects them spatially; the same material palette connects them visually. Typography stays outside the detailed models to preserve readability.

- **Semigroup / 半群** (8–38 s): concatenate formal strings. Modern glyphs are visual translations, not archaeological reconstructions. Chinese and English are separate writing traditions.
- **Action / 作用** (38–70 s): an ideal constant-gravity flow acts on phase space. The apple falls at 51–55 s. Collision is an artistic ending, excluded from the reversible model.
- **Composition / 复合** (70–103 s): light travels through composable layers. The model is an illustrative network, not a simulation or a complete Transformer.
- Prologue and coda place operations in a broader narrative; the coda identifies groups specifically with invertible symmetries.

The user-provided [reference video](https://www.bilibili.com/video/BV1MFtC6gEhY/) informed the brass rings, miniature mechanisms, rising scenery and cinematic traversal. No footage, music, branding or extracted assets from that video or the television series are used. Models, map and label textures are generated locally by `scene.mjs`; `cover.svg` is an original vector illustration. Three.js and typefaces reuse this repository's existing licensed assets. Historical source links and short mathematical derivations appear in the page's “数学注脚”.

## Controls

Space: play/pause. Left/right: seek five seconds. 1/2/3: chapter. Drag: orbit around the current scene; wheel: zoom. Return-camera button restores the narrative route. Settings control speed, quality, captions, dust, repeat and reduced motion. Opening settings does not stop the film. There are no audio tracks, video embeds, telemetry, AI API calls or external runtime requests.

Reduced-motion users start with a static view, and may explicitly play. WebGL failure retains an illustrated fallback and access to all mathematical notes. A single deterministic timeline drives cameras and models, so seeking is reversible. Settings are stored under `operations-atlas-v1`.

## Development and verification

Serve the repository root with `python3 -m http.server 8766` and open `/visuals/test-module/`.

Run `node --test visuals/test-module/story.test.mjs`. These tests check timeline boundaries, portrait/landscape camera continuity, the gravity-flow action law including inverse time, and the order and associativity of composition. The in-page algebraic arguments are proofs; finite automated examples are regression checks, not replacements for proofs.

Browser checks cover loading removal, all chapter boundaries, pause and seek, settings while playing, notes, manual camera and reset, quality, end-of-film and repeat behavior, no audio elements, and responsive layouts. UI controls use native buttons, range inputs and dialogs. Fullscreen exit does not navigate.
