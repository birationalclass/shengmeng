# Lemma 4.1: source action on the ORIGINAL global Hom charts

Original Lemmas 4.1/4.2 and the main Linearity Theorem remain OPEN.
This is an independent locally compiled/audited component, not a new full-project checkpoint.

Let K be a field. Let R -> S be a finite graded map of commutative K-algebras,
with the original gradings and graded scalar action. Let a in R be degree one;
for the native dual comparison assume R -> R[a^-1] is injective.
Set A0=(R[a^-1])0, B0=(S[phi(a)^-1])0, f:Proj S -> Proj R,
U=D_+(a), Hglobal=Gamma(U,Hom_O(f_*O,O)),
Haffine=Gamma(Spec A0,Hom_O(g_*O,O)), where g:Spec B0 -> Spec A0.
Let G:Hglobal -> Haffine be the SAME previously constructed original chart map.
Let D be mathlib's actual coextension of R along R->S, with its original S-action
and original constructed dual grading. Let T=(D[phi(a)^-1])0 and E0 the SAME
original base-to-source degree-zero chart map. Let gamma be the SAME original
native base-chart to GLOBAL Hom comparison.

Then G(b*h)=b*G(h) for ALL b in B0 and h in Hglobal, with actual source actions.
Moreover gamma(E0^-1(b*d))=b*gamma(E0^-1(d)) for ALL b in B0 and d in T.
The proof uses the verified ORIGINAL roundtrip G(gamma(ell))=Psi_affine(ell).
No different comparison map or source-compatibility certificate is supplied.
The original positive-degree weighted Hom-chart source-action formula is also proved.
No normality, smoothness, freeness or Cohen-Macaulay hypothesis is added.
The actual generic module pushforward is a module sheaf over f_*O_X;
restriction to O_Y recovers the SAME original pushforward by identity on EVERY section.

Thirteen canonical LF modules were compiled serially. All nineteen exact types and
axioms were audited using canonical-only LEAN_PATH: sixteen proofs and three definitions.
Only propext, Classical.choice and Quot.sound occur. Unchanged parent sources match
checkpoint180 or separately audited published components; their caches were reused.
The closure, pinned toolchain, lake manifest, successful compiler logs, exact types and
CheckAxioms.lean are included. Linear.lean repeats the successful audit's root imports;
it is not a separately compiled entrypoint. Local Lean runs use the protected runner:
one compiler, 8 GiB hard Job limit, two threads, 25% CPU and twenty minutes.

Bundled B0-linear GLOBAL chart-equivalence experiments reached the memory guard;
they are NOT accepted, NOT included, and their holds are retained. This component
instead proves the SAME ORIGINAL maps' source-action formulas directly.
Failed weighted-overlap revalidation is likewise excluded. No whole-project CI claim.

Still required: source action on EVERY actual native pushforward section and the SAME
entire global module-sheaf comparison; identification with H^-r of the GENUINE normalized
dualizing complex and the projective canonical twist. D is NOT a definition of omega.
Original 4.1, its omega(r+1) -> O(m) embedding, 4.2 and main theorem remain UNPROVED.
