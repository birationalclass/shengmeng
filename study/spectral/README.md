# Spectral Sequence — Study Atlas AT·002

Three main sections: initial data (K, δ₁, δ₂, D); induced structures (total cohomology, filtration and pages, exact examples, representative corrections); meaning of convergence (boundedness, comparison map, kernel proof and naturality).

Chinese/English switching preserves the mathematical notation and current interaction state. The selected language persists locally. All sections share the same numeric coordinate window, with dashed continuation arrows at its edges. These continuations are not individual differentials. Finite examples explicitly specify every nonzero space.

## Presentation and interaction

The title slide leads directly to the cumulative double-complex definition. The space and first-quadrant assumptions are stated there; there is no separate bigraded-space slide. Later slides use numbered Definition, Proposition, Lemma and Theorem blocks. The double-complex definition has a dedicated cumulative build: spaces, horizontal arrows, vertical arrows, square-zero identities, then anticommutation. Hover/focus on the next explanation or use manual controls. Revealed elements persist. Dashed continuation arrows join the same horizontal/vertical reveal layers and hover groups as the corresponding solid arrows; they still denote omitted terms, not a single differential. Hidden explanation cards reserve their final space. The SVG, coordinate axes, and node groups persist throughout navigation. The graph is visible immediately; formula annotations are added with hover, focus, click, or manual controls. Arrow keys and Space advance annotations and then definitions. Hover or keyboard focus links a formula to its geometric object; clicking pins that highlight. All differential arrows remain solid. No automatic playback is exposed. Zoom controls are separate from pinning. Three closing questions offer optional self-checks. Fullscreen supports an embedded-browser fallback.

`slides.css` controls the slide proportions, typography, reveal transitions, and user-triggered emphasis, including reduced-motion behavior. Filtered-cycle and boundary formulas annotate the coordinate diagram without identifying their subspaces with page quotients.

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

Run `node test.mjs` (Node with BigInt support). It checks the double complex identities, each dᵣ², dim Eᵣ₊₁=dim ker−dim im, stable graded filtration dimensions, total cohomology, expected nonzero d₂/d₃, and negative indices. Browser QA covers all steps, all finite examples, direction highlights, manual reveal stages, hover/focus/pinning, solid arrow strokes, λ, the empty filtration boundary, keyboard-accessible nodes, the study entry, and mobile overflow. Bilingual QA traverses every step in both languages, checks for untranslated Chinese text in English mode, and verifies that switching languages leaves the formula sources unchanged.

## Sources

J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., CUP, 2001: Definitions 2.2–2.5, Theorem 2.6 and its proof, Theorem 2.15. The exposition and examples here are an independently written adaptation to the accompanying double-complex lecture note, not copied book text.


The lecture keeps a single 0–4 coordinate window mounted across all sections. Axes and node groups retain their identity and position; definitions add overlays and update notation on that grid. Hover/focus/click on formulas or the next-step button advances annotations; there is no automatic playback or separate “show diagram” step. Taking cohomology updates E₀ to E₁ and then E₂ in place and removes the previous page's differential. The general window does not assume terms outside it vanish; the finite examples remain explicit computations. Arrow tips have fixed SVG user-space dimensions, with fine strokes and no pulsing glow.


Responsive rendering uses the measured diagram viewport with a shared 840×525 coordinate plane. SVG shapes and a separate HTML/KaTeX label layer scale together; labels are not embedded in SVG foreignObject. A ResizeObserver fits the diagram to the pane without subtracting a fixed constant from browser height. Compact and narrow layouts preserve a readable minimum size; very short windows can scroll. Chromium and WebKit checks cover continuous resizing, nine viewport sizes, label registration, language switching and fullscreen.

Hover and pinning track a single source item; shared mathematical concept tags only select diagram objects, not other definition cards. The common grid ends at (4,4), with 25 nodes and boundary continuations.
