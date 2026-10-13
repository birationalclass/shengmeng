# Original Lemma4.2: actual native projective Laurent comparison and Cech vanishing

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
The genuine canonical/normalized-dualizing identification remains UNVERIFIED.

Let K be a field, r a natural number and X=Proj(K[x_0,...,x_r]).
Let T_k be the ACTUAL integer-twist sheaf constructed by original homogeneous
fractions, and let the ordered Cech complex use the actual coordinate opens
D_+(x_i), their actual intersections and actual restriction maps.

For every integer k, each actual factor is base-linearly isomorphic to the
free module on finite homogeneous Laurent weights of total degree k whose
negative support is contained in the factor's coordinate tuple. These maps
commute with ALL actual faces, including deletion of the first coordinate.
The first-face change of frame is the actual structure-ring unit (x_1/x_0)^k.
Negative integer powers and the original localized values are proved directly.
Thus the ACTUAL geometric ordered Cech complex is isomorphic to the explicit
Laurent-weight complex, with its full alternating differential.

For k>=0, every homogeneous Laurent weight has a coordinate outside its
negative support. Its support-restricted ordered complex is contracted by
insertion at that coordinate. A cochain on this finite coordinate cover has
finitely many active weights; projection, contraction and finite assembly
therefore prove exactness in EVERY positive degree of the ACTUAL native
integer-twist ordered Cech complex. No vanishing or comparison certificate,
Cartier pole-model identification or extra smooth/normal hypothesis is assumed.

Reused proof code is the minimal fully reviewed part of CBirkbeck/AINTLIB at
ab1451487da02cd4483d0e2cdb2cc9e44bbbac17. Actual-native integer section frames,
coordinate-ratio comparison, all actual-native face maps, the native-complex
isomorphism and the transfer to exactness are constructed here. Full foreign
projects, scripts and unverified declarations are not imported.

31 new LF modules, 6186 physical source lines, 227 exact
declarations: 159 proofs (including named instances) and
68 definitions. Closed source contains 60
modules; all 29 older dependencies match earlier
immutable frozen archives byte-for-byte. Exact types and transitive axiom
checks pass with only propext, Classical.choice and Quot.sound.

One compiler, 8GiB hard Windows Job memory, two threads, CPU25%, 20min timeout.
Whole-project checkpoint180 and full-project CI status remain unchanged.

Still OPEN: eventual vanishing for the original embedded coherent sheaf,
the bound before ALL original iterates, comparison with actual sheaf cohomology,
original ideal-sheaf identification and ambient homogeneous polynomial lifting,
genuine canonical identification and the original Lemma4.1 nonzero section.
Exactness for native coordinate twists alone does NOT prove original Lemma4.2.

Reproduce with pinned lean-toolchain and lake-manifest, compiling included
Linear modules in dependency order, then CheckAxioms.lean. The convenience
Linear.lean entry is not a newly accepted whole-project checkpoint.
