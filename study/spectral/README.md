# Spectral Sequences — Study Atlas AT·002

Three main sections: initial data (K, δ₁, δ₂, D); induced structures (total cohomology, filtration and pages, exact examples, representative corrections); meaning of convergence (boundedness, comparison map, kernel proof and naturality).

Chinese/English switching preserves the mathematical notation and current interaction state. The selected language persists locally. The initial data diagrams use symbolic indices and ellipses, with no differential drawn across an omitted sequence of columns or rows; finite examples expand every nonzero space.

## Conventions

- First-quadrant cochain double complex, δ₁ of bidegree (1,0), δ₂ of bidegree (0,1), δ₁δ₂+δ₂δ₁=0.
- D=δ₁+δ₂ and FᵖCⁿ=⊕ᵢ≥ₚKⁱⁿ⁻ⁱ. The visual slanted box selects **one total degree**, not the whole subcomplex.
- E₀=Gr C; d₀ is the map induced by D, canonically identified with δ₂. E₁ is vertical cohomology; d₁ is induced by δ₁ on that cohomology.
- McCleary's cochain subspaces Zᵣ, Bᵣ (Theorem 2.6 proof): Eᵣ=Zᵣ/(Zᵣ₋₁ in the next column + Bᵣ₋₁). Subscripts of B are not shifted to another convention.
- θ: E∞ → Gr H is the canonical convergence isomorphism. Computed quotient bases are choices; no canonical splitting of the H filtration is claimed.

## Implementation

`algebra.js`: BigInt rational arithmetic, exact row reduction, filtered cycles/boundaries, quotient representatives and induced differential matrices. The three finite examples explicitly specify all nonzero generators and arrows. Other terms really are zero. In the conceptual view, the grid is only a window and is labelled accordingly.

`app.js`: accessible SVG + KaTeX labels; module navigation, animation, parameter controls, exact matrix inspector.
`content.js`: mathematical exposition. `language.js`: English translations, interface strings and persistent language selection. `vendor/`: local KaTeX 0.16.22, its fonts and MIT license. No CDN or API is required. `spectral.pdf`: accompanying lecture note.

## Validation

Run `node test.mjs` (Node with BigInt support). It checks the double complex identities, each dᵣ², dim Eᵣ₊₁=dim ker−dim im, stable graded filtration dimensions, total cohomology, expected nonzero d₂/d₃, and negative indices. Browser QA covers all steps, all finite examples, direction highlights, play/pause, λ, the empty filtration boundary, keyboard-accessible nodes, the study entry, and mobile overflow. Bilingual QA traverses every step in both languages, checks for untranslated Chinese text in English mode, and verifies that switching languages leaves the formula sources unchanged.

## Sources

J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., CUP, 2001: Definitions 2.2–2.5, Theorem 2.6 and its proof, Theorem 2.15. The exposition and examples here are an independently written adaptation to the accompanying double-complex lecture note, not copied book text.
