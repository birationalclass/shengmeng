# Cube operation order lab

A full-viewport companion to the three-dimensional Rubik notebook, at `rubik/play/`.
It supports cubes of sizes 2–5 and computes the exact order of a chosen operation sequence.

## Conventions

- Sequences act from left to right, using exact integer rotations of sticker positions and normals.
- Each sticker is individually identified. High-order center permutations count, but rotation of a single center sticker in its own plane is not recorded.
- The spatial frame is fixed. Whole-cube moves count; changing the camera does not.
- `2R` is the second layer from the right; `Rw` turns the two outer layers; `3Rw` turns three. The parser also accepts inverses, half turns, repeated parentheses, commutators, and conjugates.
- A sequence induces a permutation. Its order is the least common multiple of its disjoint-cycle lengths. Both orders and iteration counts use BigInt; large powers are computed without simulating every repetition.

The first manual turn starts a fresh recording from the identity. Subsequent manual turns append to it. Loading an algorithm, selecting an example, and changing cube size start from the identity; invalid layer references remain visible as input errors.

## Checks

```sh
node model.test.mjs
# With Playwright and Chrome available, and a local site server:
CUBE_LAB_URL=http://127.0.0.1:18975/courses/abstract-algebra/rubik/play/ node browser.test.cjs
```

Model checks include independent three-by-three face permutations, every layer/span on sizes 2–5, inverse identities, and order minimality. Browser checks cover repetition counts, interruption, reset, exact state jumps, layer selection, fullscreen, and mobile layouts.

| Sequence | 2×2 | 3×3 | 4×4 | 5×5 |
| --- | ---: | ---: | ---: | ---: |
| `R U` | 15 | 105 | 420 | 420 |
| `[R,U]` | 6 | 6 | 6 | 6 |
| `2R U` | 9 | 8 | 20 | 140 |
| `Rw U` | 36 | 120 | 240 | 1680 |

The original three-by-three notebook and its fixed-center reachability certificate remain independent of this model.
