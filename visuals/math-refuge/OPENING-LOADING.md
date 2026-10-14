# Opening resource pipeline

Edit the original modules and styles; the page runs `refuge-app.js`, `refuge-social.js`, `refuge-meter.js` and `refuge-style.css`. Generated chunks stay in this directory so assets relative to `import.meta.url` keep their original base. The builder normalizes versioned imports to one module instance and preserves dynamic imports for the lecture and upper lounge.

Build with esbuild 0.28.2 installed through npm/pnpm outside the published repository:

```
node build-opening-bundles.mjs <absolute-path-to-esbuild-package>
node build-startup-resources.mjs
node build-opening-bundles.mjs <absolute-path-to-esbuild-package>
node build-startup-resources.mjs
```

The second pass includes the updated startup resource manifest in the meter. `opening-bundles.json` records the exact output files to publish. Run `opening-performance.test.mjs` together with the auth, arrival, staged startup, demand loading and preview priority tests.

P0 supplies the actual campus exterior and water. Once the user enters, P0 hall textures download/decode at concurrency two while P1 lecture modules and fonts prepare. A single scheduler publishes and uploads textures. Required work uses timer turns without the optional 100 ms cooldown. Required boards are painted and uploaded even when the hall is outside the initial camera view. Shader warmup uses the actual output pipeline; the opening keeps its shader/shadow/resolution configuration stable. P2+ remains behind the opening/movement gate and loads on demand.

`#world` exposes `criticalTimings`, `criticalElapsedMs` and whole-flight `openingPerformance` for verification. Whole-flight samples retain stalls over 50/100 ms rather than discarding them from a rolling FPS window. Startup manifest sizes are uncompressed resource bytes, not wire usage. Account checking is bounded independently of scene readiness.
