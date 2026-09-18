# Equivariant Mixed Hodge Structure

Bilingual interactive notes using the Spectral Sequence course’s reading interface.

## Reading interface

Golden sand is the default theme. The cover, icon toolbar, framed statement abbreviations, themed cursor, continuous left-hand cards, current formula emphasis, diagram above a brief explanation, and More proof dialog follow the spectral course. The toolbar remains bright while the pointer is inside its region and dims when it leaves; there is no inactivity timer. The cover reuses the spectral course’s CSS and full-title slice animation, including metal sheen, supporting-copy reveal, and Chinese font options.

Enter, Space and the right arrow advance formulas and sections; the left arrow goes back. The reading rail jumps directly to any section. Settings control theme, autoplay, delay, looping, animation duration and reduced motion. Diagram parameters are inside settings.

## Mathematical conventions

The first-quadrant double complex uses delta_1 and delta_2, with the sign included in delta_2, and total differential D = delta_1 + delta_2. F denotes its column filtration and the induced filtration on total cohomology. L denotes the transported filtration on simplicial cohomology. The Hodge filtration is separately denoted F_Hdg.

Finite-filtration convergence, weight degeneration, and the naturality of their comparison maps are distinguished. Mixed Hodge compatibility and proper descent are stated as foundational inputs. Source documents are under sources/.

## Rendering

All formula labels use local KaTeX. SVG geometry and HTML labels share one 800 by 450 coordinate plane. Diagram colors read the active theme. The content adapter notebook-content.js synchronizes the original content with the spectral course’s notation.

## Reading order

1. Simplicial schemes: the simplex category, functorial definition, face and degeneracy maps, identities, split degeneracies, morphisms and the Čech nerve.
2. The specific singular-cochain double complex of complex varieties, its signed differentials and total complex.
3. The transported filtration L and the Hodge-theoretic input, with smooth projective hypotheses introduced explicitly here.
4. Equivariant comparison: statement, action, first pages, convergence, weight degeneration, naturality and representatives.
5. Nodal-curve example and proper descent.

The foundational definitions follow Stacks Project, Sections 14.2–14.3 and 85.26. Generic double-complex algebra is linked to the spectral course rather than repeated.

## Precise references

Both courses provide a toolbar locator and copyable `#entry=1.9&part=2` links. Links open the referenced subsection and emphasize its requested item. Cross-course links use BroadcastChannel to reuse an already loaded, same-origin, updated course tab; otherwise a named target opens a new tab. Browser focus policies may keep the source tab foreground. Tabs on another origin or still running an old build must be refreshed before cooperating.
