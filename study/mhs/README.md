# Equivariant Mixed Hodge Structure

A bilingual, continuous interactive study note by Sheng Meng. The central objective is Theorem 1 of `MHS_EQUIV.pdf`: the canonical comparison

`alpha_{p,q}: Gr_L^p H^{p+q}(X_bullet,Q) -> E_2^{p,q}`

is an isomorphism of pure Hodge structures of weight q and commutes with the actual induced endomorphisms.

## Mathematical scope

- Each X_p is a finite disjoint union of smooth projective complex varieties.
- A simplicial endomorphism f_bullet is given. No semisimplicity or invertibility hypothesis is added to the central theorem.
- h is the alternating sum of face pullbacks, v = (-1)^p d_sing, D = h + v.
- W_w H^n = L^{n-w} H^n; F is induced from the de Rham model.
- Deligne's MHS construction, Hodge compatibility of the spectral sequence, and proper descent are identified as foundational inputs.
- Finite-filtration convergence gives rho; weight degeneration gives sigma. The proof checks equivariance of both, then composes alpha = sigma^{-1} rho.
- The nodal-curve example distinguishes the original E_1 terms from their normalized row complex.
- Descent to a singular variety is applied only with an equivariant hypercover; arbitrary endomorphisms are not asserted to lift automatically.

## Interface

One continuous notebook, progressively revealed collapsible statements, a persistent unframed diagram, controls directly below it, and an independent mathematical proof panel. Chinese/English, cover, fullscreen, Enter/arrow navigation, adjustable animation duration, and reduced motion are supported.

All mathematical diagram labels use local KaTeX. SVG geometry and HTML math labels share one 800 × 450 coordinate container and the same responsive transform, including in WebKit. Dashed arrows only indicate omitted continuation; actual differentials and morphisms are solid. Higher differentials lie within each page plane. Grid points represent bidegrees, not dimensions.

Taking cohomology is shown by restricting to kernels, forming the quotient by incoming images, and only then displaying the new page. It is not drawn as a linear map on all of the preceding page. Proof-step buttons do not change the diagram state.

Source PDFs are preserved under `sources/`. No source PDF was edited. Deligne and Weibel links point to the primary mathematical sources.

## Validation

Served with the site's static HTTP server. The browser checks cover all 13 sections, all 43 independent proof steps, every diagram control, Chinese/English, responsive layout, and mathematical rendering errors. Chrome and WebKit are both checked. Separate motion checks exercise interrupted transitions, folding endpoints, pulse endpoints, quotient formation and cleanup of outgoing diagrams.
