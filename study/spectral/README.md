# Spectral Sequence — Study Atlas AT·002

A bilingual interactive notebook using a first-quadrant cochain double complex. The loading cover leads into one continuous reading surface. Definitions, propositions and theorems appear progressively and fold independently. Enter and the right arrow advance the reading sequence; the left arrow goes back. Local diagram controls and mathematical proof steps remain independent of that sequence.

The two sections use compact number-and-object headings; the current item is enlarged, while previously introduced entries stay available. Mathematical objects use KaTeX in both languages; the descriptive title remains available as a tooltip. The fold button stays at the right edge.

## v89 · Element traces, quotient classes and persistent filtered diagrams

The initial definitions share one origin-selection policy. In 1.2, 1.3 and 1.5, clicking a K tile with both indices at most 3 replays the corresponding horizontal, vertical or anticommutation trace. One-step images stop in their target terms; the two mixed paths cancel at their common target centre. The selected origin is local to the current entry and resets on changing entries. Item 1.7 retains its stricter index bound of 2. Its two formula lines exchange enlarged/resting sizes smoothly without shrinking the current heading or hiding a revealed D² = 0.

Item 1.10 now writes [a] ↦ [Da] on the left and defines both cosets in the exposition. Its finite quotient animation starts at K^{1,1}: framed class tokens follow both component maps, then the horizontal token contracts to [0] because its representative belongs to F^{p+1}. The vertical token stays put. This does not identify the entire horizontal K-space with zero. The same geometry and motion tokens drive the overlay, reduced-motion endpoint and cleanup.

Items 1.11 and 1.12 retain the existing 25 K tiles and the shared rounded diagonal filtration outlines. Both examples use p = q = 1 and r = 2. Z tests images from F^1 C^2 against F^3 C^3; B takes images from F^{-1} C^1 = C^1 and retains those in F^1 C^2. D always raises total degree by one. Particles represent whole total cochains, not individual K components; their labels crossfade from a_i to Da_i (or b_i to Db_i). Blue images meet the condition, gold images do not. Independent exposition steps give the concrete basis and component maps behind the animation. `filtered-demo.js` records this finite double complex, including a nonclosed element in Z_2 whose excluded-column components cancel.

E_0, E_1 and E_r now use the same quotient definition, generated centrally by `filtered-notation.js`. The unchanged total-cochain formulas for Z and B are explicitly extended to the auxiliary index −1; this does not define a negative page. The E_0 exposition proves Z_0 = F^p, Z_{−1}^{p+1,q−1} = F^{p+1}, and B_{−1} ⊆ F^{p+1}, so the quotient equals Gr. Both subspace entries have an independent auxiliary-index explanation. The preceding-page cohomology property remains restricted to r≥1.

In 2.3 the page-index axis is dimmed and has a clipped, left-to-right glint with a five-second period. The glint never moves the axis or page layers and is disabled under reduced motion. Page names E_0, E_1 and all later E_r retain their math typography and colors without visible title frames.

Toolbar controls retain fixed bilingual widths, have hit areas of at least 44 × 44 pixels and sit away from the top edge in fullscreen. Diagram overlays remain below the toolbar and never receive its pointer events.

Validation: Chromium checked all 48 allowed origins of the three extended traces, intermediate/end states, rapid replay, 1.7 emphasis swaps, quotient-token morphing, independent proof tabs and cleanup. The filtered example was checked exactly for bidegrees, both square-zero identities, anticommutation, all eight images and filtration membership. Browser checks also cover native fullscreen button centres and edges, three viewport sizes, touch and reduced-motion phone-landscape emulation, bilingual typesetting and the E_0 bridge.

## v88 · Preserve revealed square-zero notation on reverse navigation

In 1.7, reversing from D² = 0 retains the formula at the shared resting size while the entry heading stays current. Only the next reverse step leaves 1.7 and reduces its heading. Revealed content and the current substep now have separate state; returning to the cover still resets the reveal. All panel variants share their existing resting-size token, so leaving the entry does not resize the formula again.

Item 1.6 is named Total object / 总对象, including its abbreviation in the exposition. Item 1.8 has only the bilingual sentence explaining that D² = 0 from 1.7 makes (C^bullet,D) a complex.

Validation: Chromium sampled the reverse animation frame by frame, confirming continuous visibility, intermediate font sizes and an unchanged heading. Further checks cover a second reverse, replay, bilingual text, the single-sentence exposition, cover reset and reduced motion, without browser or KaTeX errors.

## v87 · Filtered subspaces belong to section 1

The filtered cocycle and boundary definitions now follow Filtration and Graded functor as 1.11 and 1.12, in the same section-1 frame. Section 2 returns to E_0, d_0, E_1, d_1, E_r, d_r and the convergence material as 2.1–2.10. The underlying definitions, diagrams and independent proof steps are unchanged.

Both sections now use one shared frame/folding owner. The reading order, outline rail, section selection and reopening all use the same section membership. Previous entries remain available without automatic folding; backwards navigation from 2.1 returns to 1.12.

Validation: Chromium checked the full forward and reverse sequence, manual entry and section folding, rail reopening, bilingual headings, the E_1 layer and narrow-window layout.

## v86 · Filtered cocycles and boundaries before the first page

Following McCleary, Theorem 2.6, proof on printed p. 34, the original filtered-complex subspaces Z_r and B_r are now introduced separately as 2.3 and 2.4, before E_1. The first-page entry moves to 2.5 and the remaining entries continue through 2.12. Shared definitions in `content.js` keep the first-page prerequisites and the general-page construction consistent.

The diagrams show Z_1 as a preimage condition and B_0 as D(F^p C^{n-1}) inside F^p C^n. The latter uses nested regions because D preserves the filtration. Independent exposition steps explain the representative conditions, Z_0, B_0, and monotonicity; they distinguish filtered total cochains from kernels/images on a page. The source link opens the actual textbook definition.

Validation: Chromium checked the complete forward/reverse sequence, all eight independent proof steps, bilingual headings and formulas, a single section-2 frame, narrow-window overflow, and the visible E_1 layer after the new prerequisites. Phone landscape emulation also checked both new entries, bilingual typeset notes, and overflow. No KaTeX or browser errors were reported.

## v84 · Equality anchors and staged total differential

Diagram total-degree labels align the actual equality glyph in `:=` with their grid column: the source uses the centre of K^{2,4}, and the paired target uses K^{4,4}. The shared label-plane helper recomputes the anchor after formula changes and viewport scaling. Validation covers every animation frame for n = 0…4, four viewport sizes, language switching, fullscreen, and the rotated phone reader; observed errors were below 0.01 CSS pixels.

Item 1.7 has two reading stages within the same numbered entry. First D and its animation appear; no timer advances it. The next Enter/right-arrow/tap reveals D² = 0 with the shared accordion motion and plays its own trace. Left-arrow reverses these stages, and returning from 1.8 enters the second stage. A selected tile origin persists between the two stages and resets on leaving the entry.

Item 1.6 retains only the degree-n definition on the left. The C^bullet := Tot^bullet K abbreviation is explained in the bilingual exposition below the diagram. The degree sweep and fixed summand anchors remain unchanged.

## v83 · Reading interactions, stable formulas and loading progress

Both formulas in 1.6 are separate interaction targets for the same degree sweep, `n = 0,1,2,3,4`. Moving between them can replay a completed sweep; formula clicks also replay it without requiring a mouse hover. An in-progress sweep remains a single shared animation. Validation covers both formulas in both languages, mouse hover/click, mobile taps, persistent diagram nodes and cancellation on reading advance.

The visible “Mathematical exposition” heading is removed. Its single-row layout gives the recovered height to formulas and proof steps while preserving the divider and an accessible bilingual section label.

Current numbered entries retain full brightness; other entries fade to 55%, with 82% hover/keyboard preview. The total-degree exposition reserves five fixed summand slots, keeping the equals sign and earlier K terms stationary while new factors fade in. Empty future slots contain no mathematical terms.

The final 35% of total loading progress now advances on each completed math/active font face, font-set readiness and the two layout frames. It no longer waits at 65% for the entire font batch. Resource failures cannot reach 100% or enable reading; the existing shared CSS interpolation smooths each genuine milestone.

The separate figure controller is removed. While 1.7 is current, clicking K^{p,q} with 0 ≤ p,q ≤ 2 replays D or D² from that term and updates the total degree and representative formula. Other terms and other reading entries cannot choose an origin. The default origin is K^{1,1}, restored when changing entries. Item 1.10 is titled “Graded functor / 关联分次函子”.

## v82 · Separate reading-rail gutter

The outline and card padding share `--reading-rail-width`, `--reading-rail-inset`, and `--reading-rail-clearance`. Panel-style and responsive padding now consume that gutter instead of overriding it with smaller values. Rail marks remain inside its width even when highlighted; the entire rail has at least 12 CSS pixels of horizontal clearance from each card frame. Validation covers all three styles at 320–1440px, hover, navigation across sections, fullscreen, bilingual switching and the phone landscape viewport.

## v81 · Landscape reading after the phone cover

The phone cover retains its current orientation and shows a bilingual landscape-reading hint. Start reading opens a same-origin landscape viewport; in portrait it rotates the whole reader, including SVG, HTML math, controls and pointer coordinates. A physical device rotation resizes that viewport without recreating it or changing the current entry. Cover restores the normal outer cover. Fullscreen remains owned by the outer page; native landscape locking is optional and only attempted from the active reader, with the same layout working when that API is unavailable.

`mobile-reading.js` owns entry, readiness, cleanup, sizing and fullscreen coordination. `styles/mobile-reading.css` keeps the short landscape viewport in two columns, preserves the diagram's natural scale and gives the right column scrolling space for its controls and exposition. Desktop and fine-pointer windows retain the existing layout.

Validation: Chromium phone emulation at 320×568 and 390×844 checks portrait entry, horizontal entry, physical viewport rotation with reading state preserved, taps, both swipe directions, keyboard separation, language/settings/cover controls, fullscreen and the unsupported-native-API fallback. SVG and math-label centres agree within 0.01 CSS pixel. Desktop entry remains frame-free. This is emulation coverage, not physical Safari testing.

## v80 · Midpoint reading focus

`reading-focus.js` places the current numbered entry's top at the visible screen midpoint. If its bottom would exceed the reading viewport, it moves up only enough to fit; an oversized entry starts near the viewport top. Clamping to the available scroll range leaves early entries naturally higher. Trailing space supports the final entry without adding a leading spacer. One fractional scroll follower handles section transitions, folding, style/viewport changes and fullscreen; manual wheel or touch scrolling suspends it until another entry is selected. Validation covers both boundary cases, 320–1440px widths, reduced viewport height, style and language changes, reverse navigation, and a settled transition without a final jump. The 2.10 title is now simply “收敛 / Convergence”.

## v78 · Panel styles, associated graded, and stable cover lettering

Settings now provide three persistent presentation styles: **Editorial notebook** (default), **Ordered workbench**, and **Quiet glass**. `panel-style.js` owns selection and bilingual labels; `styles/panel-style.css` owns shared presentation tokens and the three complete variants. Switching style leaves reading position, proof selection and live diagram nodes intact. The right diagram remains unframed. Existing glass backgrounds no longer override the selected presentation.

After 1.9, **1.10 Associated graded complex** defines both `Gr_F^p C^n := F^p C^n / F^{p+1} C^n` and `Gr_F^p D^n`, sending the coset of `a` to the coset of `Da`. `associated-graded.js` provides four independent exposition steps: the quotient and its elements, well-definedness of the induced differential, its square-zero identity, and the column isomorphism. The graph offers quotient and induced-map views, with controls for degree and filtration. An off-window target is not declared zero. Section 2 then names these constructions `E_0^{p,q}` and `d_0^{p,q}`. Reference: [Stacks Project, Section 12.24](https://stacks.math.columbia.edu/tag/012K).

The cover entrance moves clipped bands of the same fully shaped title, retaining those bands when they settle. This preserves kerning, text indentation, the full-width metal gradient and compositing at the end of the motion; there is no switch from individually typeset letters to a different static line. Resizing clears the bands and restores responsive full text. Language and font changes build a fresh entrance, and reduced motion displays the title directly.

Validation for this revision: Chromium checked all three styles and persistence/reset, 1.9 → 1.10 → 2.1 and reverse navigation, independent proof controls, keyboard separation, fullscreen label registration, 320–1920px widths, both languages and reduced motion. New formulas were parsed in strict KaTeX mode; the 142 exact algebra checks pass. For English, both Chinese cover fonts, and narrow Chinese layout, the settled glyph rectangles agree exactly; before/after title images are pixel-identical with the decorative shimmer frozen for comparison.

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

- `app.js`: continuous numbered reading navigation, local state, persistent keyed SVG layers, formula interaction and exact-example inspector.
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

## Typeset page diagrams (v29)

Page titles, selected terms, differentials and coordinate labels now use KaTeX with proper mathematical fonts and scripts, as do mathematical symbols in the controls. Native page selectors use localized page numbers. Each projected page places its SVG geometry and HTML mathematics inside one moving layer, keeping labels aligned during page formation and resizing in Chromium and WebKit. Checks include narrow screens, bilingual controls and multi-digit page indices.

## Reveal only reached statements (v31)

The coordinate introduction starts with no statement headers. Definition 1.1, its components, and subsequent propositions appear only when reached. Previously read statements remain available as collapsible cards; unseen cards are hidden and inert. A small Next control accompanies the existing keyboard navigation, including access to the optional examples. Language changes preserve progress; returning to the cover resets the reading sequence.

## Notebook animation settings (v32)

A settings button in the workspace header controls the left-hand accordion cards. The default is a 900 ms height-and-opacity transition; slide-only and no-animation options are available, with duration from 300 to 1800 ms. The panel includes a manual preview, saved browser preferences and a reset action. System reduced motion takes precedence.

Statement bodies and definition components use a shared, cancellable height animation. Reversing a fold starts at its current height. Hidden content becomes inert immediately, and is removed from layout when closing finishes. Changing motion preferences or resizing settles running folds; diagram timelines remain independent. Chromium and WebKit checks cover manual and automatic folds, reversals, preview, keyboard isolation, persistence, language changes, narrow screens and reduced motion.

## Integrated figure controls and visible cohomology (v33)

The figure and its controls now share one bordered module. Controls wrap at their natural height, and the mathematical exposition follows below. Page controls are shown only for page-related content; convergence statements recover the corresponding filtered-complex or stable-page diagram instead of retaining unrelated E0/E1/E2 planes. Small screens scroll the complete workspace rather than clipping controls or the notebook.

Taking cohomology is now an explicit four-stage interaction: the local incoming/outgoing complex, the outgoing kernel, the incoming image inside that kernel, and the quotient. The original source plane remains visible. Two representatives z and z+b travel to the same class; only the outgoing kernel is the domain of the quotient projection. Confirming the quotient assembles the next page point by point. No new page is created just by hovering or advancing a statement.

The formulas use page kernels and images directly, avoiding confusion with the filtered-complex Z_r and B_r. Negative-index terms are zero, while positive indices outside the display window remain actual terms. Checks cover E0 to E1, general-page bidegrees, zero incoming/outgoing spaces, representative motion, projection handoff, responsive controls and synchronized exposition in Chromium and WebKit.

## Visible page generation and lower mathematical exposition (v35)

The unframed figure has responsive top spacing. Entering the E1 proposition, or choosing to take cohomology, now runs one finite animation that forms the next page. Source terms pulse, the next plane unfolds, its cohomology terms appear in sequence, and its differential appears afterward. E0 uses columns, E1 uses rows; these are page objects rather than a claimed linear map between whole pages. Replay is explicit and reduced motion skips the animation.

The local complex, kernel, image inclusion, and quotient are optional tabs inside the mathematical exposition below the figure. Changing a principle does not hide the generated page or restart its animation. The quotient projection has domain ker(d_r), and the displayed E1 identification retains H^q(K^{p,bullet},delta_2). Generated pages remain visible while inspecting the principles.

## Differential definitions, independent proofs, and continuous endpoints (v36)

Left-hand statements specify domains, targets and representatives for d0, d1 and dr. The mathematical exposition owns separate topic and proof-step controls. It proves descent to the associated graded, the projection isomorphism Phi0, the identity Phi0 d0 = delta2 Phi0, representative independence for d1, and numerator/denominator compatibility and square zero for dr. Definitions and proof conventions were checked against McCleary, Theorem 2.6 and its proof, and Theorem 2.15. The total differential remains D = delta1 + delta2.

Source-dot pulses return to their actual resting opacity and color. Newly inserted graph elements use their eventual style rather than a hard-coded opacity. Interrupted emphasis fades back; coordinate and term entrances can finish independently. Accordion targets track the changing natural content height during formula scaling. The 2D/3D handoff crossfades only at aligned geometry, and retired element traces fade away. The proof controls leave page-animation DOM untouched. Chromium and WebKit tests cover the definitions, all 11 proof steps, bilingual/mobile display and page generation; 66 graph-opacity endpoints and a natural-height accordion endpoint were checked, including projection cleanup.


## Definition notation and filtered subspaces (v38)

Defining formulas use `:=`; computations retain `=` and canonical identifications retain `\cong`. Statement and inner-definition fold controls use plus when closed and minus when open.

Selecting Z_r or B_r in Definition 2.3 now opens its own total-space diagram: a preimage condition for Z_r, and the intersection of D(F^{p-r}C^{n-1}) with F^pC^n for B_r. The image arrow targets the full image, not the intersection. Region sizes encode no dimensions. The independent exposition supplies four proof steps for each, including column cancellation conditions and monotonicity. Controls vary n, p, and r, including zero-degree and vanishing-filtration cases. Page controls remain reachable when the E_r view is active; the existing page-evolution state is retained.

## Explicit input and total-complex demonstrations (v39)

The square-zero card is neutral: only its two formula buttons start the corresponding trace. Leaving a formula for the card padding restores a static state and cannot start the other trace. The same rule applies to the compound total-differential card. Enter is captured for the reading sequence regardless of focus; it enters from the ready cover, advances one item, and cannot click, pin, fold, replay, select a page, or toggle fullscreen. It is ignored while a modal dialog is open. Pointer and Space activation remain available.

The total-complex reveal runs one finite sweep through n=0,1,2,3,4. Integer labels and direct-sum terms update together while the grouping outline interpolates in the fixed grid. The last degree remains visible. The total-differential reveal splits an element into its horizontal and vertical images and adds them in C^{n+1}, outside individual K-terms. The D² button follows all four paths: the two pure terms vanish separately and the two mixed terms cancel at their shared K^{p+1,q+1}. It never combines elements from different K-summands as though they lived in one K-term. Replay controls stay beneath the figure. Pointer exit does not replay a different demonstration.

Chromium and WebKit checks cover both square-zero exits, focus on native buttons/sliders, exclusive Enter navigation, modal isolation, the five-degree sweep and stable viewport, final D/D² states, D² exit, Space replay, bilingual controls, and narrow layouts.


## Shared presentation system and revised reading order (v40)

The single notebook starts with §1 Double complex (seven inner entries through column filtration), then §2 (E₀,d₀), item 2.1 (E₁,d₁), item 2.2 (Eᵣ,dᵣ), and §3 convergence. Headings display numbers and names, with mathematical statement kinds kept as internal metadata. E₀'s card contains the quotient and an aligned two-line d₀ mapping definition; E₁ is introduced only in the next entry. Canonical identifications, square-zero identities and next-page cohomology live in the right-hand Key properties and proof-step area. Enter advances the reading sequence; the separate Next button is removed.

The loading line interpolates real progress with a subtle glow. The cover waits for user entry. Formula changes crossfade individual changed tokens; MathML always describes the current formula. The total-degree caption is larger and has enough height for superscripts. Term brightness, borders and glass tint share the same timing as the grouping sweep; SVG elements retain their identity instead of being replaced.

D² has two visible applications of D, with a pause and a second split inside both intermediate K blocks. Pure terms vanish separately; the mixed terms cancel in their common target. Filtration uses the same indexed-sweep renderer as Cⁿ, shrinking along one diagonal as p increases. Its component-particle demonstration maps into the next-degree filtration; every target has first index at least p. Particle counts do not encode dimensions or assert surjectivity.

| Module | Responsibility |
| --- | --- |
| `styles/tokens.css` | Shared palette, glass, muted levels, typography, scrollbar and motion tokens. |
| `styles/diagram.css` | Terms, maps, groupings, page points, common emphasis and reduced motion. |
| `styles/math.css`, `math-transitions.js` | Token-level formula crossfades, larger degree captions and properties layout. |
| `styles/cover.css` | Loading cover, progress, sheen and entry controls. |
| `styles/scrollbars.css` | Inset rounded scrollbars shared by notebook surfaces and dialogs. |
| `style.css`, `slides.css` | Base page layout and responsive notebook/accordion/control layout. |
| `visual-style.js` | Read CSS motion tokens in JavaScript. |
| `diagram-dom.js` | Patch SVG in place and preserve live transition state. |
| `total-animations.js`, `filtration-animations.js`, `element-trace.js`, `page-evolution.js`, `filtered-view.js` | Mathematical timelines and state-specific geometry. |
| `content.js`, `algebra.js`, `differential-proof.js`, `workbench.js` | Definitions, exact calculations, properties and proof exposition. |
| `app.js` | Reading sequence and coordination of content, diagrams and controls. |

Edit shared tokens/rules to change the style. Do not add per-definition copies of colors or fade durations. Mathematical timelines may retain distinct stages and pauses; generic emphasis and fades read the common tokens.

Validation includes Chromium and WebKit, continuous opacity samples, persistent SVG identity, shared timing and palette changes, superscript-only transitions and rapid interruption cleanup, D²'s two-stage split, filtration particle targets, exclusive Enter navigation, 390/1024/1920px layouts, cover readiness/retry and reduced motion. The exact algebra suite checks 142 page/convergence cases.


## Double-complex entrance (v41)

Entering from the cover opens §1 Double complex immediately. Its first reveal expands both axes about the actual (0,0) lattice point, then pops the 25 terms in a short diagonal stagger. SVG tiles and their HTML KaTeX labels use matching transforms; the axis mask appears with each tile. Tick labels only fade, without displacement. Introducing δ₁ first fades the p-axis and its label, then grows every horizontal map from its source. δ₂ does the same for the q-axis and vertical maps. Differential arrows stay solid; continuation arrows retain their dashed style.

`initial-animations.js` owns the entrance timeline. All durations come from `styles/tokens.css` through `visual-style.js`; `styles/diagram.css` owns axis visibility and SVG transform conventions. Generic insertion fades defer to an existing child animation. Hover, language changes and resize do not restart the entrance. Rapid forward input preserves the current entrance, while leaving it settles interrupted effects. Returning to the space entry does not hide and recreate existing terms. A new cover entry replays the opening; reduced motion goes directly to the same final state.

Validation covers the axis-before-tile and axis-fade-before-map order, paired tile/formula scaling, solid arrows, stationary fading ticks, rapid forward/reverse input, cover restart, reduced motion, local hover, bilingual rendering and 390–1920px layouts in Chromium and WebKit. The E₀ projection, E₁/E₂ generation and later page/filtration controls remain in the existing reading sequence.


The exposition has a fixed heading beneath its divider and an independent scrollport. The figure controls use a reserved row within the visualization, so changing the controls or proof length cannot move that heading. New topics return the exposition to its top. On narrow screens the same two regions keep separate content scrolling.

The first-quadrant condition now appears in the exposition rather than the left K-family declaration. It specifies vector spaces over one field, or left modules over one ring; δ₁ and δ₂ are respectively linear maps or module homomorphisms. Square-zero relations explain the ordinary row and column cochain complexes. Item 1.4 traces one element along the two mixed routes, retains the opposite results in their common K^{2,2}, then combines them into zero. The explanation connects this cancellation and both square-zero identities to D²=0 and the cohomology of the total complex. The existing total-differential timeline supplies the shared particle rendering, cancellation and smooth retirement.


## Compact reading toolbar (v42)

The top bar contains only language, animation settings, cover and fullscreen controls. The former site-navigation links, brand block and notation/reference dialog are removed from this notebook header. The lesson heading displays only “Spectral Sequence”, without the Study Notes eyebrow. `styles/toolbar.css` owns the shared toolbar sizing, title spacing and fullscreen offset; the same controls remain available above the notebook in fullscreen and on narrow screens. Cover loading and entry are unchanged.

After the cover is entered, the reading surface is initially empty. The first Enter reveals Double complex and starts the axes-then-terms entrance. The diagram and exposition retain their layout slots while hidden, so this first reveal does not shift the coordinate system or page layout.

On that first Enter, the left definition frame expands from a small point at its upper-left corner. Its layout rectangle is reserved throughout; the heading and formulas fade in near the end of the expansion. This uses the shared initial timeline and honors the notebook's disabled-animation option and system reduced motion.

Validation: Chromium and WebKit verify blank entry, first-Enter frame and axis animations, the four-control toolbar, language/settings/cover actions, native or embedded fullscreen layout, and 320/390/1024px widths with no overflow or page errors.


## Title in the reading toolbar (v43)

“Spectral Sequence” is now on the left of the top toolbar, with the four reading controls on the right. The duplicate heading inside the workspace is removed. On narrow screens, the title and controls occupy two compact rows in the same toolbar; the fullscreen workspace offset follows that toolbar height.

## v44 · Frame before content

All left-hand card entrances and accordion openings share one sequence in `notebook-motion.js`: finish the frame geometry, then fade in text and formulas. The fade is started by the geometry animation’s completion, including new cards, nested definitions, and the settings preview. Right-hand diagram animations have separate ownership. Disabled/reduced motion still shows the final state immediately.

## v45 · Anticommutation cancellation

Mixed-composite particles brake on their original horizontal/vertical paths before meeting. A plus sign briefly marks their midpoint inside the common target term; the particles accelerate into it, shrink into zero, and the plus fades with the particles. There is no terminal sideways offset. Total differential and total-square timelines remain independent.

## v46 · Addition at the target centre

The anticommutation plus sign, particle merge, and final zero share the exact centre of the target K tile. Particles retain the existing slowdown and approach along their original incoming arrows.

## v57 · Open notebook layout

Removed the enclosing workspace border, shadow, and contrasting surface. The toolbar divider has more breathing room, and its Chinese title uses the same shared serif font stack as the cover. Toolbar heights still drive fullscreen offsets; short windows scroll the reading surface while preserving a usable diagram height.

The K introduction now simply says that each term is a vector space, in both languages. On entering 1.3, the horizontal square-zero trace completes before the vertical trace starts; the pair runs once, and direct interaction or leaving 1.3 cancels the remaining sequence.

Diagram controls now follow the canvas directly. Removed the freestanding total-trace captions and scope notes from the plot-to-controls gap; their mathematical content is in the exposition panel. Initial diagrams crop only the unused lower caption strip, while all SVG and formula layers retain the same scale.

The initial K diagram adds horizontal/vertical ellipses above and to the right after the last tile appears. The total differential is one declaration, `D := δ₁ + δ₂ : Cⁿ → Cⁿ⁺¹`; its particles stop at the horizontal and vertical target summands. Repeated diagram descriptions were removed from the bilingual exposition, while the filtered-quotient proofs and convergence conditions remain. The D² panel now starts with the expansion and its cochain-complex consequence.

Integrated the separately published cover and saved font settings. Shared title tokens keep the reading title consistent with the selected cover typeface. §2 opens its exposition with the quotient origin of E₀ and d₀ = Gr(D): column projection identifies d₀ with δ₂, not with the total differential D. The construction requires only (C,F,D). See Stacks Project, Tag 012M, for the associated-graded construction.

Validation: Chromium and WebKit checked the combined total-differential formula at 320–1440px, stationary target particles after completion, D² cancellation, bilingual formula rendering, and the 320–1920px/fullscreen layouts. The first square-zero pair and cancellation-on-navigation checks passed in both engines. The merged cover/font settings and all five E₀ proof steps were also exercised.

## v58 · One numbered item per reading page

Every numbered definition or statement now occupies one reading step. Enter advances within a section before opening the next section; Left reverses the same sequence. §2 uses 2.1–2.8 and §3 uses 3.1–3.13, avoiding the old duplicate numbers. A map and its representative formula, and the two sides of a split equality, stay on the same numbered page.

`reading-pages.js` owns the semantic grouping and shared transition: fade out the old item, resize the frame while empty, then fade in the new item. Interrupted navigation settles to the newest requested page. Diagram hover and proof navigation remain separate from the reading position. The old rounded annotation border is removed; E₀ appears first, followed by d₀ on its own page. Initial definitions use the same single-item policy while keeping the accumulated diagram.

Validation: all 28 numbered items were traversed forward and backward in Chromium and WebKit. Checks cover single-item visibility during transitions, rapid navigation, grouped map/equality formulas, independent proof controls, and bilingual 320–1440px layouts.
