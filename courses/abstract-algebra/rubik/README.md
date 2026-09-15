# Rubik’s Cube & Group Theory

Interactive companion to Sheng Meng’s abstract algebra course. The page is silent and has no external runtime dependency. KaTeX and the licensed fonts are shared with existing pages in this repository.

## Mathematical conventions

Products act from left to right: `(a b)(x) = b(a(x))`. Fixed centres; 48 mobile facelets. Every quarter turn is an exact integer rotation of positions and normals. Camera rotation never changes the permutation. Corner and edge orientation conventions are explicitly defined in Chapter 6.

Chapter 7 proves the reachability theorem with a transparent finite certificate: orientation and parity invariants give the upper bound; certified words fixing earlier base points give orbit-size lower bounds whose product meets it. The checker does **not** assume that the supplied generators form complete stabilizers. The independent verifier only needs finite permutation products, inverses, fixed-point checks, and orbit traversal.

## Verification

```sh
node test.mjs
```

The tests compare all six face permutations to the independent Harvard GAP cycles, check orientation composition and reconstruction on a deterministic 2,000-turn walk, validate named examples and algorithm parsing, verify the full order certificate, reject corrupted certificates, and parse all formulas with KaTeX.

Browser checks cover pointer face turns and orbiting, keyboard operation, algorithm playback/seek/pause, reset during playback, undo/redo, impossible-state indicators, all lesson routes and proofs, certificate verification, settings persistence, and responsive layouts. The app uses Canvas 2D with controls and complete state data also available as accessible HTML.

## Rebuild the certificate

Install SymPy 1.14.0 in your Python environment, then run:

```sh
python3 generate-certificate.py
node test.mjs
```

Set `RUBIK_NODE` if Node is not on PATH. SymPy discovers straight-line words. The generated `certificate.json` is subsequently checked without SymPy by `certificate.mjs`.

## References

- Janet Chen, *Group Theory and the Rubik’s Cube*: https://people.math.harvard.edu/~jjchen/docs/Group%20Theory%20and%20the%20Rubik%27s%20Cube.pdf
- Independent GAP generators: https://people.math.harvard.edu/computing/gap/index.html
- Interaction study: https://js.cubing.net/cubing/twisty/ and https://www.cubing.net/touch/
- Design study: https://www.vitsoe.com/us/about/good-design

The page implements its own cube model and rendering. The design extends the site’s spectral notebook layout and muted golden sand palette.
