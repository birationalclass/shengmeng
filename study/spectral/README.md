# Spectral Sequence — Study Atlas AT·002

A bilingual interactive course using a first-quadrant cochain double complex. The main presentation has exactly **four slides**: title, Initial data, Induced structures, and Convergence. Footer buttons and arrow/Space keys move only between those slides. Topic tabs, operation buttons, formula hover/focus, sliders and exact examples operate within the current slide. Nothing plays automatically.

## Mathematical interaction design

| Definition | Coordinate diagram | Operation panel and interpretation |
| --- | --- | --- |
| δ₁, δ₂ | Add horizontal or vertical maps independently. | Domain, codomain and bidegree. Nodes are vector spaces. |
| δ₁²=0 or δ₂²=0 | Emphasize two consecutive solid arrows and mark the zero vector at the endpoint. | The composite is zero; neither individual map nor its target space is required to vanish. |
| Anticommutation | Compare the two paths around one adjacent square. | The two composites sum to zero; they need not vanish separately. |
| Cⁿ | A slanted dashed boundary groups the full degree-n diagonal. | The enclosed factors form a direct sum, denoted Cⁿ, not a new K-node. |
| D | Domain and target diagonals have different colors. | D:Cⁿ→Cⁿ⁺¹ adds the two contributions to each component. |
| Hⁿ | Locate degree n and the relevant incoming/outgoing degrees. | Bⁿ⊆Zⁿ⊆Cⁿ, followed by the quotient map **Zⁿ→Hⁿ**, not a map from all of Cⁿ. |
| FᵖCⁿ | Select a segment of one diagonal; p>n gives the empty segment. | Inclusion and D:FᵖCⁿ→FᵖCⁿ⁺¹. |
| E₀ | Identify the selected column; a second boundary locates the projection kernel. | Projection FᵖCⁿ→Kᵖⁿ⁻ᵖ has kernel Fᵖ⁺¹Cⁿ. |
| E₁, E₂ | Nodes update in place; old differentials disappear after cohomology. | Identify incoming image and outgoing kernel, then quotient. d₁ acts on E₁, not on K. |
| Zᵣ, Bᵣ, Eᵣ, dᵣ | Distinguish total-complex conditions from page nodes. Adjustable r preserves displacement (r,1−r). | Preserve McCleary's precise denominator; use D on representatives before passing to the quotient. |
| Convergence | Locate filtered cocycles, show the vanishing target condition, then highlight the relevant E∞ position. | Construct FᵖHⁿ by an image, send the same cocycle through the comparison, compute the kernel, and identify E∞ with Gr H. No canonical splitting is asserted. |

Nested regions encode subspace inclusions only, not dimensions or chosen complements. Quotient maps explicitly start from the indicated inner subspace. The general convergence view is separate from the finite examples; a dimension equality is not used as its proof.

Hover/focus previews one source item. Click pins it; leaving a preview restores the pin or the selected local operation. Relationships never count as additional presentation slides. Square-zero effects are finite opacity transitions, with no coordinate movement, timer-driven playback or looping animation. Reduced-motion preferences disable these transitions.

## Implementation and conventions

- `app.js`: four-slide navigation, local state, persistent keyed SVG layers, formula interaction and exact-example inspector.
- `workbench.js`: bilingual local topic/action labels and semantic diagrams of direct sums, inclusions, quotients and representative maps.
- `content.js`, `language.js`: formal statements, proofs, translations and persistent language selection.
- `algebra.js`: exact BigInt rational arithmetic, filtered cycles/boundaries, representatives and induced differential matrices.
- `slides.css`: responsive layout and operation diagrams. KaTeX math occupies an HTML plane scaled together with SVG; no SVG foreignObject is used.

The same 25 coordinate nodes, indexed 0–4, remain mounted. General terms outside this window are not assumed zero. Dashed arrows continue the displayed rows/columns and are not individual differentials. Actual differential arrows are solid. For n=4, the next total-degree diagonal extends outside the displayed window; the formula for C⁵ still includes all its factors.

The convention is δ₁:(p,q)→(p+1,q), δ₂:(p,q)→(p,q+1), δ₁δ₂+δ₂δ₁=0 and D=δ₁+δ₂. The column filtration is decreasing. For r≥1:

Eᵣᵖᑫ = Zᵣᵖᑫ / (Zᵣ₋₁ᵖ⁺¹,ᑫ⁻¹ + Bᵣ₋₁ᵖᑫ).

θ:E∞→Gr H uses the same closed representative on both sides. Choosing computed bases does not specify a canonical splitting of H.

## Validation

`node test.mjs` checks the exact algebra engine. Browser checks cover four-slide navigation, independent directions, square-zero and anticommuting paths, pin restoration, local quotient operations, removal of previous-page differentials, every formal view in English, 25 persistent nodes, nine viewport sizes, SVG/HTML label registration, fullscreen, and access to exact-example matrices. Chromium and WebKit are both exercised. Source/build checks are separate from the mathematical explanations above.

## Reading

J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., CUP, 2001: Definitions 2.2–2.5, Theorem 2.6 and its proof, and Theorem 2.15. The accompanying `spectral.pdf` uses the same double-complex notation. This site is an independent exposition and implementation.
