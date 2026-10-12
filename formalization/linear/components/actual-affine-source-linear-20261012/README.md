# Lemma4.1: actual affine source compatibility

The original Lemma4.1, Lemma4.2 and Linearity Theorem remain OPEN.
This is an independently checked component, not a full-project checkpoint.

Let A and B be commutative rings and let A->B be an algebra map.
Set f:Spec B->Spec A and H=Gamma(Hom(f_*O_SpecB,O_SpecA),Spec A).
The ORIGINAL coextension D=coextendScalars(A->B)(A) is B-linearly
equivalent to this ORIGINAL H, with action (b.h)_W(x)=h_W(b|_W*x).
The equality Phi(b.d)(x)=Phi(d)(b*x) is proved by actual element
evaluation; no scalar-compatibility or generation certificate is assumed.
For EVERY actual A-injective resolution I of A,
H^0(coextendScalars(A->B)(I)) is isomorphic to H AS A B-MODULE.
No finiteness, normality, smoothness, freeness or CM condition is imposed
in these affine statements. This is NOT the normalized-dualizing
identification or the projective omega_V(r+1)->O_V(m) embedding.

Four canonical LF modules were freshly compiled in sequence, followed by
an exact six-declaration type/axiom audit from canonical-only LEAN_PATH.
Only propext, Classical.choice and Quot.sound occur. Unchanged dependency
sources match fully checked checkpoint180 or the separately audited
source-action/derived-zero component. Dependency caches were reused;
an uncached full-project build or new whole-project GitHub Lean CI is
not claimed. Failed resource-limited global-overlap experiments are excluded.

Review manifest.json and evidence/exact-types-and-axioms.txt. The pinned
source closure, toolchain, lake manifest and exact CheckAxioms.lean are
included. The Linear.lean package entry consists only of the same four
imports used by the successful audit. On the author's Windows machine,
all compiler invocations use lean_runner.run_file: one compiler, 8 GiB
hard Job limit, two threads, 25 percent CPU, 20 minute timeout. Never
launch an unprotected parallel rebuild on the user's computer.

Remaining: the SAME original projective chart/global Hom comparison
must preserve the source action; then identify the result with H^-r
of the genuine normalized dualizing complex and its projective twist.
