# Original Lemma4.2: actual integer-twist finite presentations

Original Lemma4.1/4.2 and the Linearity Theorem remain OPEN. The genuine
canonical identification remains UNVERIFIED. Original hypotheses,
numbering and one fixed degree before every iterate are unchanged.

Let K be a field, S an actual Noetherian graded K-algebra, M a finite
actual integer-graded S-module. Assume actual degree-one basic opens cover
Proj(S). Then EVERY integer-degree native local-fraction sheaf T_k(M) is
finitely presented, hence finite type and quasicoherent. This does not
assume a shifted decomposition or a finite-presentation certificate.

Define M[k]_d=M_(d+k) on the SAME underlying module. Its internal direct
sum and homogeneous S-action are proved. The ACTUAL local-fraction
predicates, localized values, original ring actions and restrictions give
an O_Proj-linear sheaf isomorphism T_0(M[k]) ~= T_k(M), with identity on
actual localized section values. Its inverse is constructed. Previously
verified degree0 finite presentations transfer to EVERY k.

Let b:E -> F be an actual homogeneous module map, with E finite over the
actual Noetherian S and the same actual degree-one cover. For EVERY k,
the ACTUAL categorical kernel of its native sheaf map is finitely
presented. Ordinary module kernel finiteness, its internal grading and
native-to-categorical kernel comparison are derived. E need not be free,
b need not be surjective. The degree0 predecessor is also included.

A separate necessary Serre-presentation step was minimally reused from
CBirkbeck/AINTLIB: an actual epimorphic quotient of a finite-type module
sheaf is finite type. Its actual site/sheafification hypotheses are printed
in the exact declaration audit; no quotient certificate is supplied.
The source is commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17,
ForMathlib/SheafModuleFiniteTypeQuotient.lean, Apache2.0, itself adapted
from Vilin97/Clawristotle. Original attribution is preserved.

This ACTUAL regrading isomorphism is not yet a comparison with the Serre
tensor-power line-bundle model M~ tensor O(k). That comparison, the same
original ideal sheaf I_V, uniform eventual H1 vanishing, ambient
polynomial/global-section comparison and the Koszul/proper-duality
nonzero-section production remain OPEN. Finiteness is not cohomology
vanishing. No original4.1/4.2 completion is claimed.

Six new canonical LF modules:8 proofs,4 definitions,12 exact declaration
and standard-axiom audits. The 144-module closed source contains138
byte-identical checkpoint180 dependencies and six new roots.337 physical
new source lines include comments and blanks. Every inline-annotated
new definition is included in the exact audit. Compiler/resource logs
and exact types/axioms are included. Only propext,Classical.choice and
Quot.sound occur. One compiler,8GiB hard Windows Job,two threads,CPU25%,
below normal,20-minute timeout. Largest accepted root compile5.15GiB,
accepted final audit4.20GiB. Failed drafts are not counted.
Linear.lean is a reproducibility import entry, not separately compiled.
This independent local component does not promote full-project CI or
checkpoint180 and does not alter previous frozen releases.
