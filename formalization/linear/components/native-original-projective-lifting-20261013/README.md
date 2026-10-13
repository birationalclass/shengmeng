# Actual ORIGINAL projective polynomial lifting and nonzero extension

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
The genuine canonical/normalized-dualizing identification remains UNVERIFIED.

Let K be a field, sigma a finite nonempty ordered set, S=K[x_i], and I an
ACTUAL homogeneous prime ideal. Let V=Proj(S/I) with its ORIGINAL quotient
grading and native homogeneous-fraction twist T_N. Primality is the original
integrality condition, not an added normal, smooth or Cohen--Macaulay input.

Then there is ONE natural bound B(I) before ALL N>=B(I) and ALL actual
global sections s of T_N on ORIGINAL V, such that an ORIGINAL homogeneous
polynomial Q in S_N has section [Q]/1=s. No global polynomial lift, chart
bijection or overlap equality is supplied as a hypothesis.

The proof constructs actual base/source chart bijections from existing
Noetherian quasicoherence and source torsion-freeness. Source chart overlaps
agree, including charts where a coordinate has zero image in S/I. Actual
sheaf gluing gives an ambient quotient-module section. Previously audited
ambient uniform polynomial lifting gives Q. Injectivity of the BASE chart
map is proved from the actual comap of the generic source prime; this does
not assume the quotient module is torsion-free over the polynomial ring.
Exact fraction formulas and integer regrading transfer [Q]/1 back to the
same ORIGINAL quotient-Proj section. A full pushforward sheaf isomorphism
and derived cohomology comparison are NOT claimed or assumed.

For the ORIGINAL integral complex projective equations V in P^n, specialize
the same bound before ALL N and ALL actual sheaf monomorphisms F -> T_N.
Then a nonzero global section of F extends to an ORIGINAL degree-N polynomial
Q outside the ORIGINAL ideal I(V). The monomorphism and nonzero section are
explicit ACTUAL inputs. Their original4.1/Koszul existence, the genuine
canonical identification and original4.2's all-iterate vanishing integration
remain open; this partial release does not declare either original lemma
or the main theorem complete. The bound depends only on V, not on an
iterate, map, monomorphism or section.

13 new LF modules, 787 physical source lines and 24 exact
declarations: 20 theorem proofs and 4
definitions. Definitions are counted separately from theorem proofs.
Closed source contains 343 modules; all 330
older dependencies preserve earlier immutable frozen code: 329
match byte-for-byte and 1 differs only by CRLF to LF.
The normalized older dependency is freshly compiled and separately type/axiom
audited; its former archive hash and exact transformation are recorded.
Exact types and transitive axioms pass with only propext, Classical.choice
and Quot.sound; no unfinished proof or additional custom logical input.

Older dependencies retain their recorded Apache2.0 CBirkbeck/AINTLIB and
mathlib attribution. This release constructs the uncovered original-Proj
chart/global transport and original polynomial extension against unchanged
pinned Lean/mathlib revisions. Prior immutable source archives are retained.

One compiler, 8GiB Windows Job hard memory, two threads, CPU25%, 20min timeout.
Whole-project checkpoint180 and full-project CI status remain unchanged.
Reproduce with pinned lean-toolchain and lake-manifest: compile the included
Linear modules in dependency order, then CheckAxioms.lean. The convenience
Linear.lean entry is not a newly accepted whole-project checkpoint.
