# Spectral Sequence — Study Atlas AT·002

A bilingual interactive course using a first-quadrant cochain double complex. The main presentation has exactly **four slides**: title, Initial data, Induced structures, and Convergence. Initial data reveals its six definition items in place before advancing to Induced structures. Enter, the right arrow and the forward button advance this sequence; the left arrow and previous button reverse it. Space also advances when no interactive item has focus. Topic tabs, operation buttons, formula hover/focus, sliders and exact examples operate within the current slide. Nothing plays automatically.

## Mathematical interaction design

| Definition | Coordinate diagram | Operation panel and interpretation |
| --- | --- | --- |
| δ₁, δ₂ | Reveal horizontal and then vertical maps with their definitions; hover re-emphasizes an already introduced map. | Domain, codomain and bidegree. Nodes are vector spaces. |
| δ₁²=0 or δ₂²=0 | Emphasize two consecutive solid arrows and mark the zero vector at the endpoint. | The composite is zero; neither individual map nor its target space is required to vanish. |
| Anticommutation | Compare the two paths around one adjacent square. | The two composites sum to zero; they need not vanish separately. |
| Cⁿ | A slanted dashed boundary groups the full degree-n diagonal. | The enclosed factors form a direct sum, denoted Cⁿ, not a new K-node. |
| D | Domain and target diagonals have different colors. | D:Cⁿ→Cⁿ⁺¹ adds the two contributions to each component. |
| FᵖCⁿ | Select a segment of one diagonal; p>n gives the empty segment. | Inclusion and D:FᵖCⁿ→FᵖCⁿ⁺¹. |
| E₀ | Identify the selected column; a second boundary locates the projection kernel. | Projection FᵖCⁿ→Kᵖⁿ⁻ᵖ has kernel Fᵖ⁺¹Cⁿ. |
| E₁, E₂ | Nodes update in place; old differentials disappear after cohomology. | Cohomology is treated as known. d₁ acts on E₁, not on K. |
| Zᵣ, Bᵣ, Eᵣ, dᵣ | Distinguish total-complex conditions from page nodes. Adjustable r preserves displacement (r,1−r). | Preserve McCleary's precise denominator; use D on representatives before passing to the quotient. |
| Convergence | Locate filtered cocycles, show the vanishing target condition, then highlight the relevant E∞ position. | Construct FᵖHⁿ by an image, send the same cocycle through the comparison, compute the kernel, and identify E∞ with Gr H. No canonical splitting is asserted. |

Nested regions encode subspace inclusions only, not dimensions or chosen complements. Quotient maps explicitly start from the indicated inner subspace. The general convergence view is separate from the finite examples; a dimension equality is not used as its proof.

Hover/focus previews one source item. Click pins it; leaving a preview restores the pin or the selected local operation. Revealing a definition updates the existing main slide; hover effects do not consume a presentation step. Square-zero effects are finite opacity transitions, with no coordinate movement, timer-driven playback or looping animation. Reduced-motion preferences disable these transitions.

## Implementation and conventions

- `app.js`: four-slide navigation, local state, persistent keyed SVG layers, formula interaction and exact-example inspector.
- `workbench.js`: bilingual local topic/action labels and semantic diagrams of direct sums, inclusions, quotients and representative maps.
- `content.js`, `language.js`: formal statements, proofs, translations and persistent language selection.
- `algebra.js`: exact BigInt rational arithmetic, filtered cycles/boundaries, representatives and induced differential matrices.
- `slides.css`: responsive layout and operation diagrams. KaTeX math occupies an HTML plane scaled together with SVG; no SVG foreignObject is used.

The same 25 coordinate nodes, indexed 0 through 4, remain mounted. Negative-index rows, columns, and tick labels are omitted from the display. General terms outside this window are not assumed zero. Dashed arrows continue the displayed rows/columns and are not individual differentials. Actual differential arrows are solid. For n=4, the next total-degree diagonal extends outside the displayed window; the formula for C⁵ still includes all its factors.

The convention is δ₁:(p,q)→(p+1,q), δ₂:(p,q)→(p,q+1), δ₁δ₂+δ₂δ₁=0 and D=δ₁+δ₂. The column filtration is decreasing. For r≥1:

Eᵣᵖᑫ = Zᵣᵖᑫ / (Zᵣ₋₁ᵖ⁺¹,ᑫ⁻¹ + Bᵣ₋₁ᵖᑫ).

θ:E∞→Gr H uses the same closed representative on both sides. Choosing computed bases does not specify a canonical splitting of H.

## Validation

`node test.mjs` checks the exact algebra engine. Browser checks cover four-slide navigation, independent directions, square-zero and anticommuting paths, pin restoration, local quotient operations, removal of previous-page differentials, every formal view in English, 25 persistent nodes, desktop and narrow viewports, SVG/HTML label registration, fullscreen, and access to exact-example matrices. Chromium and WebKit are both exercised. Source/build checks are separate from the mathematical explanations above.

## Reading

J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., CUP, 2001: Definitions 2.2–2.5, Theorem 2.6 and its proof, and Theorem 2.15. The accompanying `spectral.pdf` uses the same double-complex notation. This site is an independent exposition and implementation.

Initial data presents the double complex and its total complex in one definition panel. Eight local items contain names and mathematical expressions only; prose descriptions and the separate Total complex tab are removed. Hovering or pinning C or D updates the same diagonal groups and operation panel, without changing the main slide.

The initial assumptions use rendered K^{p,q} notation and omit a base-field symbol. The initial panel has no explanatory prose. Double complex, δ₁, δ₂, the square-zero identities, anticommutation, C^bullet D, F and E₀ are introduced in order, with corresponding graph layers synchronized to each reveal.

The coordinate axes intersect at the centre of the (0,0) node. Nonnegative tick labels follow those axes. An SVG mask suppresses axis strokes behind term labels, including dimmed terms.

## Multi-page view and first-paint loading (v16)

Initial data ends with the column filtration and E₀ = Gr F C ≅ K. Induced structures starts at E₁; no elementary cohomology tutorial intervenes. E₁ and E₂ are expressed directly as cohomology. The three modules remain on the same four-slide main path.

`page-stack.js` projects (p,q,r) onto parallel oblique pages, with r increasing horizontally from left to right. Desktop shows four pages and narrow screens show two. The page-index window advances by the visible group size without an artificial final page. Each differential stays in its r-plane and has displacement (r,1-r,0). A selected bidegree is aligned across all layers. Dots represent spaces at bidegrees, not basis vectors or dimensions. A target outside the p,q window is not assumed zero; a negative q target is zero by the first-quadrant hypothesis. The third axis indexes pages; it is not a third cochain grading. No arrows join whole successive pages. Their relationship is E_(r+1) ≅ H(E_r,d_r). E∞ remains the stable object defined in the convergence proof, not a finite layer named infinity.

Layer tabs, the page selector, and individual points support inspection. The 2D definition view remains available. Mobile layouts use a more compact projection with two simultaneous pages and the same page selector. Switching layers does not consume main slides or autoplay.

Node surfaces are 68 by 38 diagram units (previously 88 by 42), with thin translucent borders and a quiet gradient inspired by msmath's GlassCardSurface. Differential endpoints and coordinate-axis masks use the same dimensions.

`boot.js` controls a minimal first-paint loading overlay. Its progress marks resource initialization, math rendering, and font readiness. The page becomes visible only after all bundled KaTeX fonts load and two paint frames pass. A failed module or font load retains the overlay and exposes Reload. There is no arbitrary minimum loading duration; reduced-motion preferences disable fades.

Chromium and WebKit checks exercise the eight initial reveals, the direct E₀→E₁ transition, 3D bidegrees, layer selection and page windows, 2D switching, bilingual controls, mobile rendering, true axis origin, compact label clipping, delayed font loads, and failed-resource recovery.

## Definition emphasis and coordinate introduction (v17)

Initial data starts with a bare coordinate frame, before revealing K. Positive tick labels sit close to the axes. Enter or Next reveals the K family and hides the redundant nonnegative tick labels. Moving backward before K restores the labels. The SVG frame remains mounted, and axis strokes are masked behind terms only after they appear. Finite examples retain numeric coordinates because their node labels do not carry bidegrees.

The current initial definition has a larger heading and formulas; previous definitions return to compact type only on the next stage. Later modules emphasize the selected local definition, without changing type sizes on hover. Each newly displayed definition triggers one finite opacity emphasis in the corresponding diagram, with no geometry movement, looping or timer-driven advance. Reduced motion disables the emphasis. Browser checks verify stage sizes, exactly one emphasis per reveal, unchanged graph bounds, reversible tick visibility, horizontal page order, and the bidegree (r,1-r,0) of every displayed differential.

The v19 coordinate window is 0≤p,q≤4. The negative-index vanishing assumption remains in the mathematical definition; its zero row and column are no longer drawn. Negative axis tails are shortened while preserving the (0,0) intersection and all positive-node positions.

Definition typography now uses a 380ms eased font-size transition on persistent DOM nodes, so previously enlarged text shrinks continuously as the next definition grows. The left pane follows the growing definition during this finite transition; the right diagram's coordinates and layout stay fixed. The two square-zero controls are centered as a group. Reduced motion makes these changes immediate.

Every displayed horizontal and vertical differential in Initial data carries its own δ₁ or δ₂ label, respectively. Labels use small colored anchors placed in the gaps between nodes, share the direction's reveal and one-shot emphasis, and dim with the other direction on hover. Dashed window continuations remain continuation marks, not additional single differentials.


## Opening sequence (v20)

The coordinate prelude contains only the right-hand coordinate frame. Its former left placeholder, scope caption, and operation card are hidden while their layout slots remain reserved. The axes expand from (0,0), followed by a quiet fade of ticks and guides. Enter/Next reveals the Double complex definition card with a 460ms fade and small upward movement, together with the K terms. These are finite navigation-triggered entrances, not automatic slide advances. Changing language, hovering, or resizing does not replay them; navigation away cancels pending effects. The opening waits for mathematical typesetting, and reduced motion shows the final state immediately.

Total-degree connecting lines are masked around every term box, including transparent glass backgrounds. Their segments remain visible only in the gaps; the enclosing dashed direct-sum region is unchanged.


## Single loading cover (v21)

The loading screen is the sole cover and names Sheng Meng. The former static title slide is removed. Once mathematics is ready, the same screen exposes Start reading and waits for its activation; no second cover appears. Fresh visits and reloads stop here even when the saved URL ends in a lesson hash. Native keyboard activation of Start is retained, while global slide keys and lesson navigation remain inactive on the cover. Entry begins the coordinate animation; returning to the cover reopens this ready screen without loading resources again.


## Cover fullscreen (v22)

The cover is headed 学习笔记 / Study Notes and has a top-right fullscreen control available before mathematics loads. A single bootstrap controller keeps cover and lesson buttons in sync; entry and return preserve fullscreen, and Escape exits. Where native fullscreen is unavailable, the existing viewport-filling study layout remains the fallback. The control does not activate Start or change the loading state.


## Stable coordinate-to-complex reveal (v23)

The 0–4 tick positions are identical before and after K appears. They fade out in 120ms without translation. Terms and the matching axis cutouts fade in after an 80ms lead, while the definition card fades at its final size; the first entry does not combine scaling, translation, and font-size growth. Unfinished axis opening animations continue smoothly if Next is pressed early. Subsequent definition typography retains its smooth enlargement/shrinking behavior.

The former rotated rectangles are replaced by compact rounded contours, formed from the endpoint term boxes with a four-unit margin. A one-factor sum gets the same rounded outline. Region geometry uses the full index range rather than clipping it to displayed nodes: for C⁵ the blue outline continues beyond the top/right window boundaries toward K⁰⁵ and K⁵⁰, instead of closing at K¹⁴ and K⁴¹. A short caption identifies those unseen endpoint terms.

Square-zero interactions now trace a foreground element through two consecutive horizontal or vertical arrows, with a moving color gradient along the solid arrow shafts. The element pauses in the middle term, shrinks at the third term, then expands into 0. This finite trace starts on hover, focus, or click, not on slide advance. Leaving the relation clears the overlay; reduced motion displays the final zero immediately.

All diagram controls (examples, degree, filtration, page and view controls) are grouped immediately below the diagram. The separate lower panel is headed 数学阐述 / Mathematical exposition. Fixed row sizes prevent control visibility changes from moving the graph.

Total-degree labels retain the standard totalization notation: Cⁿ := Totⁿ K. The diagram, source/target cards and direct-sum expansion update together with n; Cⁿ⁺¹ receives the same identification. The left definition states Cⁿ := Totⁿ K = ⊕(p+q=n) Kᵖᑫ.

## Single-page notebook and K-to-E comparison (v23)

The three topic entries share one fixed workbench. The slide footer and page count are removed. Definition, proposition and theorem cards fold independently using top-right chevrons; numbers immediately follow the statement kind. Initial definitions can be selected directly, while Enter/Right follows the reading order. Folding a statement preserves the current graph. The induced and convergence sections show all their statement headers together.

`k-to-e.js` offers three selectable visualizations: filtration/projection, parallel object layers, and a local column. Each uses the same position (p,q)=(1,2), n=3 and four manual stages K, E0, d0, E1. Stage selection updates the mathematical exposition. The projection kernel is F²C³, identifying E0¹² with K¹²; d0 is induced by D and corresponds to δ₂. E1 is the kernel/image quotient, never the result of mapping an arbitrary vector of K into cohomology. The layers describe objects, not a third cochain grading. Smooth opacity changes preserve geometry; reduced motion is respected.

## Direct comparison access (v24)

The three K-to-E designs are always visible as individual buttons under the diagram once K has been introduced. Each opens its design immediately, with the four construction steps and a return control below. No gateway button hides these choices. The redundant generic coordinate-window caption is removed; the C5 out-of-window endpoint explanation remains.

## Continuous notebook and page evolution (v25)

All definitions, propositions and convergence statements are mounted in one uninterrupted reading list. The former Initial / Induced / Convergence tabs are removed. Opening a new statement folds the previous statement without replacing the notebook or resetting the diagram. The two existing calculation examples remain as optional cards at the end.

`page-evolution.js` replaces both the three comparison prototypes and the detached page-stack renderer. The original K grid becomes E0 in place through the canonical associated-graded identification; the same SVG nodes and HTML mathematics remain mounted. Its coordinate frame is then transformed affinely into the r=0 plane. Later pages unfold sequentially, each labeled as cohomology of the preceding page. The r-axis runs left to right. Every differential stays within its own page with displacement (r,1-r,0); there are no whole-page arrows or assumed canonical maps from arbitrary cochains to cohomology. The right-hand exposition distinguishes quotient identification, induced differential, and camera/plane deformation.

Controls allow a return to flat E0, a tilt, adding the next page and inspecting previously generated pages. Hover alone does not generate pages. Finite transformations are cancellable; reduced motion completes them immediately. A display window shows four pages on desktop and two on narrow screens, without a mathematical final page.

## Clean projection handoff (v26)

The moving source reaches the projected E0 position before the page view crossfades in. The complete SVG and HTML label layer then becomes hidden and inert, including the differential labels previously omitted by the term-only fade. Glass-node filters are disabled during the projection; the page renderer owns all three axes after handoff. Reversing or interrupting the motion restores the source from the current transform. Chromium and WebKit checks cover forward, reverse, interrupted, narrow-screen and reduced-motion transitions.

## Centered source grid (v27)

The two-dimensional 0–4 grid is centered in its viewport with origin x=170 instead of x=225. Axis extents and continuation arrows derive from that origin. The projection renderer receives the same origin, preserving the source-to-E0 correspondence. Element traces retain their actual source coordinates when reduced motion is enabled mid-animation.

## Local term hover (v28)

Term nodes no longer participate in the diagram-wide concept selector. Hover and keyboard focus add only a local border highlight, preserving the active differential, total-degree/filtration region, exposition and element trace. Click/Space inspection remains available; Enter retains the notebook's next-item behavior. Chromium and WebKit checks verify six mathematical views and an uninterrupted square-zero trace.
