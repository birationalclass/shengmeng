# Milestone 39: finite free structure of actual formal thickenings

For H with exactly c equations in K[[s_r]][[z_c]], the power-ideal sandwich (z)^e <= (H) <= (z) proves all of the following without a regularity or flatness assumption:

- the actual H sequence is regular: its radical is (z), its height is c by the actual variable-regularity theorem, and the ambient ring is Cohen–Macaulay by milestone 38;
- the ambient maximal ideal is exactly (z) + (s), proved via the actual constant-coefficient map;
- H appended with the parameter coordinate sequence is regular, since it is a full parameter system in that Cohen–Macaulay ring;
- the actual quotient is finite over K[[s]] by milestone 36, and free by the existing audited regular-maximal-generator theorem. Hence it is flat.

This replaces the otherwise explicit miracle-flatness and regularity inputs for this geometric thickening setting. K is an arbitrary field, r,c are positive, and the sandwich remains an explicit input until derived from original geometric total invariance. The global Linearity Theorem is not proved.

Reuses pinned mathlib regular-sequence quotient and maximal ideal APIs, and the previously audited CM/depth ports with exact provenance. Online discovery in milestone 38 identified the official tree and local Regular/Free interface; no new downloaded setup or axiom.
