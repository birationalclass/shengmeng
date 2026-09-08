# Spectral Sequences — Study Atlas AT·002

Four connected modules: construction and column filtration; exact computation; a representative and its corrections; bounded convergence and naturality.

## Conventions

- First-quadrant cochain double complex, δ₁ of bidegree (1,0), δ₂ of bidegree (0,1), δ₁δ₂+δ₂δ₁=0.
- D=δ₁+δ₂ and FᵖCⁿ=⊕ᵢ≥ₚKⁱⁿ⁻ⁱ. The visual slanted box selects **one total degree**, not the whole subcomplex.
- E₀=Gr C; d₀ is the map induced by D, canonically identified with δ₂. E₁ is vertical cohomology; d₁ is induced by δ₁ on that cohomology.
- McCleary's cochain subspaces Zᵣ, Bᵣ (Theorem 2.6 proof): Eᵣ=Zᵣ/(Zᵣ₋₁ in the next column + Bᵣ₋₁). Subscripts of B are not shifted to another convention.
- θ: E∞ → Gr H is the canonical convergence isomorphism. Computed quotient bases are choices; no canonical splitting of the H filtration is claimed.

## Implementation

`algebra.js`: BigInt rational arithmetic, exact row reduction, filtered cycles/boundaries, quotient representatives and induced differential matrices. The three finite examples explicitly specify all nonzero generators and arrows. Other terms really are zero. In the conceptual view, the grid is only a window and is labelled accordingly.

`app.js`: accessible SVG + KaTeX labels; module navigation, animation, parameter controls, exact matrix inspector.
`content.js`: mathematical exposition. `vendor/`: local KaTeX 0.16.22, its fonts and MIT license. No CDN or API is required. `spectral.pdf`: accompanying lecture note.

## Validation

Run `node test.mjs` (Node with BigInt support). It checks the double complex identities, each dᵣ², dim Eᵣ₊₁=dim ker−dim im, stable graded filtration dimensions, total cohomology, expected nonzero d₂/d₃, and negative indices. Browser QA covers all steps, all finite examples, direction highlights, play/pause, λ, the empty filtration boundary, keyboard-accessible nodes, the study entry, and mobile overflow.

## Sources

J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., CUP, 2001: Definitions 2.2–2.5, Theorem 2.6 and its proof, Theorem 2.15. The exposition and examples here are an independently written adaptation to the accompanying double-complex lecture note, not copied book text.
