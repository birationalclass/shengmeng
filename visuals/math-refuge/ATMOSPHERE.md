# Continuous Shanghai atmosphere

The scene uses Shanghai local time (UTC+8) and NOAA fractional-year solar coordinates. Sun direction, direct and ambient light, fog, water highlights, room lighting and the sky update continuously. Time preview approaches the selected hour along the shortest arc, including midnight.

The disk has a physical baseline radius and a smooth artistic enlargement of up to 1.65 near the horizon for wide-angle readability. It is not an astronomical angular-size simulation. The ESO/S. Brunier 6000×3000 all-sky Milky Way panorama supplies the galaxy bulge, dark dust lanes, nebulae and stellar density. The diffuse galactic band and bright stars are controlled separately: a filtered texture supplies broad dust lanes, while a high-pass brightness threshold retains only sparse resolved stars. Chroma is reduced; this is a dark-sky impression rather than a quantitative naked-eye photometry model. Its linear-light exposure fades continuously through twilight and clouds occlude it. Mipmapping and anisotropic filtering limit shimmer. The fixed orientation rotates continuously but is artistic, not a date-calibrated Shanghai star chart. The image loads once (7.8 MB), fades in, and is disposed with the sky; a failed download leaves a dark sky. Attribution and CC BY 4.0 are linked in sky settings and assets/sky/CREDIT.md. A cached neutral environment probe changes intensity continuously; it is not a live sky reflection map.

Open-Meteo supplies current weather at fixed Shanghai coordinates. No user geolocation is requested. Refresh: 15 minutes. Timeout: 10 seconds. Cached observations expire after two hours. Offline fallback is visibly labelled. Cloud cover, wind-driven cloud motion and fog blend over four seconds; the rain preview models overcast conditions, not individual rain particles.

Water depth is an artistic continuous field in metres: western and southern shoals, an eastern channel and deeper open water. Beer–Lambert-style absorption blends sand/green shallows into blue depths. It is neither bathymetric survey data nor a navigational map.

Sources: https://gml.noaa.gov/grad/solcalc/solareqns.PDF and https://open-meteo.com/en/docs.

## Blackboard controls and tests

Writing speed and camera return delay live in the right-hand blackboard module. Erasers leave the board, turn outside the tray, move above it, and descend vertically; pickup reverses the path. Collision regression checks the board backing and every tray floor/lip.

stroke-test.html is a single-page proof of concept with authored centreline strokes, pen lifts, speed/seek controls and a formula-size slider (default 90%). The current preview compares the original authored strokes with refined, more compact cursive glyphs. Both use explicit pen contacts and lifts; automatic font skeleton ordering was rejected in visual review and removed from the selector. Production now defaults to the refined authored style. Blackboard settings can restore C · Marck Script (non-stroke reveal); the selection persists locally. Supported Latin letters, digits and operators follow explicit centreline contacts and pen lifts, shared by the ink reveal and chalk pose. Chinese and unsupported mathematical symbols retain their original glyphs and reveal method. Mathematical alphabets with distinct meanings remain unchanged. Nested SVG clipping and measured cover wrapping preserve layout bounds. The displayed performance numbers measure only 2D stroke drawing, excluding 3D rendering and texture uploads.

## Time panel

The top-right Time button owns all time/weather controls. Play/pause uses the selected 1×, 5×, 10×, 30× or 60× rate. The simulation wraps through midnight; real-time sync restores the Shanghai clock. Event buttons seek to three minutes before sunrise/sunset and start at the selected rate. Open-Meteo event times are preferred; local NOAA-derived horizon crossings supply an explicitly labelled fallback. These are time controls, independent of camera-tour speed.
