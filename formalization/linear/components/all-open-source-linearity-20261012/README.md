# Lemma4.1: actual affine source-linearity on every open

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
This is an independently audited component, not a full-project checkpoint.

Let Y=Spec R, alpha:O_Y -> S an actual sheaf-of-rings morphism, and M,N
actual S-module sheaves whose source scalar actions commute. Assume M
and the source algebra S are quasicoherent over O_Y. Let C:M|alpha ->
N|alpha be the SAME original O_Y-linear sheaf morphism, and assume its
map on global sections preserves S multiplication. Then, on EVERY open
W, for EVERY actual local source function b and EVERY local section x,
C_W(b*x)=b*C_W(x). No target QC or surjective restriction is required.

The proof first uses affine-QC faithfulness for global source scalars on
all local module sections. A local section x defines the actual internal
Hom section b |-> b*x. Affine-QC internal-Hom extensionality for the
source algebra then extends compatibility to ALL local source scalars.
The original base map and original source actions remain unchanged.

Actual source-ring and module chart restrictions are constructed; scalar
recovery is identity on every section. The SAME original affine-QC
extension on any original affine chart preserves every local source
scalar under its stated top-section source-linearity premise. Separately,
the SAME native pushforward comparison preserves EVERY actual source
function on the WHOLE original degree-one chart. Actual function coverage
is derived from mathlib basicOpenIsoAway, not supplied as a certificate.
The latter native statement retains localization injectivity and source
chart bijectivity as explicit prerequisites; the original-variety version
of these prerequisites was previously independently derived.

Ten new canonical LF modules plus the existing original-subopen Hom
extensionality module are freshly compiled: 11 proofs, 7 definitions,
18 exact types/axioms audited. Of these, 10 proofs and 7 definitions are
new, and one supporting proof is revalidated. Only propext,
Classical.choice and Quot.sound occur. Other project dependencies match
checkpoint180 or six independently audited published components. Matching
caches are reused; Linear.lean is an import entry, not separately compiled.
The closed source, pinned toolchain, resource/compile logs and exact audit
are archived. One compiler, 8 GiB hard Job limit, 2 threads, 25% CPU,
20-minute timeout. Held global-bundle/weighted-overlap experiments excluded.

Remaining: apply the all-open bridge to the SAME original native chart
morphism, construct/verify the entire global source-linear sheaf iso,
and identify genuine normalized-dualizing H^-r and the canonical twist.
Native coextension is NOT defined to be omega. The manuscript's original
proof uses global generation of Hom(omega_V(r+1),O_V)(m), a generically
nonzero map, and vanishing of its torsion kernel. This component does not
prove the original fixed-twist embedding omega_V(r+1) -> O_V(m), Lemma4.1,
Lemma4.2 or the main theorem. Whole-project checkpoint180 remains unchanged.
