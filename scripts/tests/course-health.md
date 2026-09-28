# Classroom diagnostics

`assets/course-health.js` is an independent, classic ES5 bootstrap used by the
algebra landing page, course portal, lesson frames, three laboratories and Group Sudoku.
The notice stays hidden when no issue has been observed and does not intercept input.
It follows the active modal/fullscreen surface and the selected language.

| Code | Observed issue |
| --- | --- |
| D-COMPAT / D-LAYOUT | Missing browser API / dynamic viewport support |
| D-ASSET / D-DATA / D-LESSON / D-CARDS | Script or stylesheet / section data / lesson initialization / card data failure |
| D-SCRIPT / D-ASYNC | Uncaught execution or asynchronous error |
| D-WAIT / D-OPENING | Startup not ready / opening animation or audio loading failed |
| D-SCROLL | Collapsed or clipped reading region, or repeated wheel input without movement |
| D-OFFLINE / D-SERVER / D-RECORDS | Browser offline / unconfirmed records sync / failed records request |
| D-MAP / D-GRAPHICS / D-STORAGE | 3D fallback / graphics context loss / unavailable local storage |
| D-MONITOR / D-NOSCRIPT / D-LOCAL | Bootstrap blocked / JavaScript disabled / file-protocol loading |

For classroom support, photograph the bottom message and record the browser name,
page and action. These are observations, not proof of a DNS, firewall or proxy cause.
The detector makes no network probes and uploads no logs or student data. Runtime
messages omit URL queries and exception payloads. Recoverable conditions clear only
when the relevant recovery is observed. Wheel boundaries and interactive canvases
are excluded. A browser process freeze, total page/network failure, or a security
policy that prevents all scripts can limit what an in-page detector can report.

With `jsdom` and `acorn` available to Node:

```sh
node --test scripts/tests/course-health.test.cjs
node courses/abstract-algebra/2026-fall/tests/course-loading-dom.test.cjs
```

Manual release checks: normal course and lesson remain quiet; section JSON 503 is
visible over the loading cover; blocked module and blocked bootstrap report their
own failures; records outage leaves guest play usable; notice remains legible in
Chinese/English, desktop fullscreen and a 390px viewport. Simulate failures locally,
never by modifying the live records service.
