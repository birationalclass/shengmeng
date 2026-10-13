# Actual native multiplication and its monomial Laurent comparison

Let K be a field, P=Proj K[sigma], and T(k) the actual integer twist
defined by locally homogeneous fractions on the original scheme. Let
p be a homogeneous polynomial of degree m>=0, and a a degree-one
coordinate nonvanishing on the original open U. Then actual multiplication
M_p:T(k)->T(k+m), constructed from the original localized scalar action,
satisfies M_p(frame_k(r))=frame_(k+m)((p/a^m)*r), for every integer k
and actual structure-ring section r. The coefficient p/a^m is constructed
using the original homogeneous localization and actual open restriction.

When sigma is finite and p=X^b is an original monomial with coefficient1,
each actual coordinate intersection's native/Laurent equivalence sends
M_p to the linearly extended shift e->e+b. Local exponent addition agrees
with the global homogeneous reindexing, including its anchor coordinate.
These global shifts commute with every Cech coface, including initial
ones, and the full alternating differential, giving actual cochain and
homology maps. Native multiplication is NOT defined by duality transport.

The component includes actual homogeneous polynomial multiplication and
its dual precomposition interface, complementary residue exponent identities,
and actual localization monomial multiplication on Laurent basis vectors.
The claim here stops at actual monomial chart comparison. General
polynomial residue-dual naturality, finite graded-presentation duality,
derived sheaf cohomology comparison and actual Koszul restriction
compatibility remain OPEN. Original4.1 canonical identification is still
UNVERIFIED; original4.1/4.2 and the main theorem remain OPEN. Original
manuscript hypotheses and numbering are retained. No extra smoothness,
normality or Cohen-Macaulay condition is added to the original integral V.

14 new modules; 625 physical source lines; 31 audited
declarations (21 proofs and 10 definitions).
93 closed modules; 79 older dependencies
match previously frozen source bytes. Exact types and transitive axioms
are included. Permitted axioms: propext, Classical.choice, Quot.sound.
All compilation and audits use lean_runner.run_file, one compiler,
8GiB Windows Job hard memory, two Lean threads, CPU<=25%, twenty-minute
wall timeout. No whole-project checkpoint/CI completion is claimed.

Pinned Lean v4.35.0-rc3, mathlib2a885768dae569d938bb9ff3474da6a8753bb90a.
Original manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile modules in dependency order, then CheckAxioms.lean. Linear.lean
is the convenience entry. Library provenance and older Apache2.0 AINTLIB
attribution are preserved. No downloaded setup program is executed.
