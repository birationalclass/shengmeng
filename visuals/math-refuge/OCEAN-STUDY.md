# Ocean Study integration

The campus imports `createOceanLayer` from `../ocean/ocean-renderer.js`; it does not duplicate or approximate the original wave solver. The original page still creates its own renderer, sky and camera. The embedded layer shares the campus renderer, camera and render loop.

Reused unchanged: the 32-component wave spectrum, authored overturning profiles, 30 Hz ping-pong foam transport, retained wetness, raised whitewater sheet, froth and spray. `ocean-study.js` adapts geographic coordinates, samples the existing campus bathymetry for shoreline/bed height, uses campus sky/cloud textures and sun direction, and replaces colour transfer with the host's tone mapping and depth-dependent transmission. The existing granular sand material reads the original foam buffer's wetness channel. Offshore water remains the existing campus material and blends through the shallow shelf.

Settings → Environment offers Ocean Study / previous sea and an independent surf sound switch. Sound uses the original filtered brown-noise synthesis, a smoothed distance gain `0.32 / (1 + (distance / 24)^1.65)`, and distance-dependent low-pass filtering. Distance includes observer height and is measured to sampled shore points. Audio begins only after enabling the switch and mutes when the page is hidden. It is procedural audio, not a recorded beach or acoustic obstruction simulation.

This is the original artistic real-time model, not a FLIP simulation. The east-facing study patch fits the current campus shelf; it does not turn every remote island into a breaking beach. Fine study geometry adds about 1.08 million triangles; standard water detail uses the original reduced mesh sizes. The architecture keeps its existing independent 1.3 million triangle budget.

The separate `../ocean/shorelines.html` experiment draws three idealized shoreline types with independent tide/time settings: a Nang Yuan inspired triple sandbar, crescent bay, and Zlatni Rat inspired gravel spit. It reuses the ocean spectrum but uses a distance-field shoreline model for these different topologies; it is a morphology experiment, not the original overturning-wave model or surveyed geography. The existing four local experiments remain intact.

Validation: 111 campus tests pass, including bathymetry, geographic placement, audio attenuation and scene assembly. Browser checks cover shader compilation, both water models, standard geometry, sound activation, three shoreline selectors and top-down view. No perceptual match to offline FLIP footage is claimed.
