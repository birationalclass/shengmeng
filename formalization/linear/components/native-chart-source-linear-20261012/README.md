# Lemma4.1: ORIGINAL native homogeneous source-chart duality is source-linear

Original Lemma4.1/4.2 and the Linearity Theorem remain OPEN.
This is an independently verified component, not a full-project checkpoint.

Let K be a field. Let R->S be a finite map of commutative K-algebras,
with their ORIGINAL N-gradings and the original graded scalar action.
Let a be an original degree-one base element, and assume R->R[a^-1]
is injective. Let D be mathlib's ACTUAL coextension of R along R->S,
with its ORIGINAL S-action and constructed original dual grading.
Put A0=(R[a^-1])_0, B0=(S[phi(a)^-1])_0, g:Spec B0->Spec A0,
and T=(D[phi(a)^-1])_0, the ACTUAL source-native degree-zero chart.
Set H=Gamma(Spec A0,Hom_OA0(g_*O_SpecB0,O_SpecA0)), with the ORIGINAL
source-section action, restricted via the ACTUAL Gamma-Spec ring iso.

Then the SAME original native source-chart comparison is an actual
B0-linear equivalence T ~= H. Its underlying map is PROVED equal to
the SAME previously constructed native affine chart comparison,
after the inverse of the SAME original base/source zero-chart map.
For every b in B0 and d in T, Psi(b*d)=b*Psi(d).
The ORIGINAL chart functional satisfies Phi(b*d)(x)=Phi(d)(x*b).
The actual source action on EVERY original Hom section is still
(b*h)_W(x)=h_W(b|_W*x). No scalar, evaluation, chart-identification
or global-duality compatibility certificate is supplied.
No normality, smoothness, freeness or CM assumption is added.

The proofs retain original numerators and denominator images through
the universal localization comparison, cover EVERY localized source
element, restrict to the ACTUAL native homogeneous chart, and compare
with the ACTUAL affine internal-Hom map. The native homogeneous
module factory already retains the native Ore scalar action on values.

Eight canonical LF modules were compiled serially: six action modules
in the first phase, two affine Hom modules in the next phase. All 19
exact declaration types and axioms were then audited together from
canonical-only LEAN_PATH. There are 17 proofs and two definitions.
Only propext, Classical.choice and Quot.sound occur. Unchanged parents
match checkpoint180 or the separately audited published source-action
and affine-source components. Their caches were reused. No uncached
whole-project rebuild or whole-project GitHub Lean CI is claimed.

The pinned source closure, toolchain, lake manifest, compiler logs and
exact CheckAxioms.lean are included. Linear.lean consists of the same
eight imports as the successful audit; it is not a separately compiled
entry point. Every local compile/audit uses lean_runner: one compiler,
8 GiB hard Job limit, two threads, 25% CPU and 20 minutes.
Failed global-overlap resource experiments and their retained holds
are excluded. Do not remove holds or start an unprotected rebuild.

Still required: source action on the SAME original PROJECTIVE GLOBAL
native-dual/Hom isomorphism, and identification with H^-r of the GENUINE
normalized dualizing complex and the projective canonical twist.
This local source-linear equivalence is NOT the omega embedding.
