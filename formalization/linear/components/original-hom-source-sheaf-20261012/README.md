# Lemma4.1: actual original Hom as a source-ring module sheaf

Original Lemma4.1/4.2 and the Linearity Theorem remain OPEN.
This independently verified component is not a full-project checkpoint.

Let f:X->Y be ANY scheme morphism and N an O_Y-module sheaf.
Set H=Hom_OY(f_*O_X,N). On every open U in Y, use the actual source
action (b.h)_W(x)=h_W(b|_f^-1(W)*x) for b in Gamma(f^-1(U),O_X).
Then H, with its ORIGINAL abelian presheaf, restrictions and sheaf proof,
is an ACTUAL module sheaf over the actual ring sheaf f_*O_X.
Restricting scalars along O_Y->f_*O_X yields an isomorphism to the
ORIGINAL O_Y internal Hom. The isomorphism is PROVED to be the identity
on every original section. No finiteness, affineness, normality, freeness,
smoothness or CM assumption is imposed on these sheaf statements.

The general change-of-action comparison is proved separately in
OriginalSheafSourceRestriction, and is then applied using the already
proved source-module, restriction and base-action compatibilities.
This split avoids the monolithic comparison that reached the memory
guard. Failed source, log and hold are retained and excluded here.

Three canonical LF modules were freshly compiled in sequence, followed
by all SIX exact declaration types and axioms from canonical-only
LEAN_PATH. Only propext, Classical.choice and Quot.sound occur.
Unchanged dependency sources match checkpoint180 or the previously
audited source-action component. Their caches were reused. No fresh
uncached whole-project rebuild or new whole-project GitHub Lean CI is
claimed. The package Linear.lean has the same three imports as the
successful audit; it is not a separately compiled entry point.

Pinned Lean version, mathlib revision, closed source, exact audit and
compiler logs are archived. All local compiler calls use lean_runner:
one compiler, 8 GiB hard Job limit, two threads, 25 percent CPU and a
20 minute timeout. Do not launch an unprotected parallel rebuild.

Still required: the SAME original projective chart/global native-dual
comparison preserves source action, and identification with genuine
normalized-dualizing H^-r and the projective canonical twist.
