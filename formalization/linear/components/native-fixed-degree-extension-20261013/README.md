# ONE original fixed degree: actual extension with actual subscheme vanishing

Original Lemmas4.1/4.2 and the main Linearity Theorem remain OPEN.
The genuine canonical/normalized-dualizing identification remains an EXPLICIT
UNVERIFIED input. The original4.2 Koszul/proper-duality construction of the
nonzero section and its restrictions is NOT proved by this release.

Let V be the ORIGINAL integral nonempty complex projective equations in P^n.
Then, from V alone, construct degree-one forms L_0,...,L_r giving an ACTUAL
finite injective linear normalization. Construct its ACTUAL native associated
normalization-dual sheaf D and ONE positive integer m before ALL subsequently
given sheaves F, identifications F~=D, nonzero sections and families of actual
subschemes. No affine-chart point, normalization or embedding is an input to
this aggregate theorem. No normal, smooth or Cohen--Macaulay hypothesis is
added to V. The auxiliary r is the constructed normalization index, not an
unproved identification with the manuscript's Scheme dimension.

The actual homogeneous dual injection is multiplied by a power of an ACTUAL
nonzero degree-one element to raise its shift above the independently proved
ORIGINAL polynomial-lifting bound. The ACTUAL sheaf map and its monomorphism
are proved; the target identification uses the proved integer equality
0+m=m. The actual target twist is locally free and quasicoherent. Compact
object definitions prevent redundant type elaboration and have no theorem
conclusion, identification, injection or nonzero-section fields.

Let an ACTUAL sheaf F have an identification with D. This identification is
the user-authorized UNVERIFIED canonical bridge; no new logical input is
introduced into Lean. The SAME m gives a constructed actual monomorphism
j:F->T_m. Let s be an ACTUAL nonzero global section and let i_a:Z_a->V be ANY
family of actual subschemes on which s pulls back to zero as its actual
structure-module morphism. Then an ORIGINAL degree-m homogeneous polynomial
Q satisfies originalSection(Q)=j(s), Q outside I(V), and the actual morphism
of its section pulls back to zero along EVERY i_a.

The structure-module morphism is built with pinned mathlib's unitHomEquiv
from the actual family of restrictions of s, with naturality proved. Its
value at the actual ring unit on V is s, and it commutes with the actual
sheaf map j. Thus pullback vanishing follows from actual functoriality;
pullback is NEVER claimed to preserve monomorphisms. The bound precedes all
degrees, sheaves and subscheme families, so it does not depend on an iterate.
Producing the nonzero s with the ORIGINAL Setup vanishings remains open.

11 new LF modules, 520 physical source lines and 16 exact
declarations: 12 theorem proofs and 4
definitions. Closed source contains 427 modules; all
416 older dependencies match prior immutable frozen
archives byte-for-byte. Exact types/transitive axioms use only propext,
Classical.choice and Quot.sound. No unfinished proof or custom logical input.

Online pinned mathlib GradedMonoid and DirectSum sources were fetched and
matched with the local cache before reuse of graded powers. Existing local
graded projections, original normalization, native sheaf maps, locally free
twists, uniform original polynomial lifting and mathlib's unitHomEquiv are
reused. Older Apache2.0 AINTLIB/mathlib provenance remains retained.

Pinned manuscript: Luo_1005-20261006.tex, SHA256
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Original4.1 is the canonical-sheaf fixed-twist embedding; original4.2 is the
fixed-degree polynomial supported away from the other original fibres.
This release checks the downstream actual construction with the precise
UNVERIFIED identification and given nonzero section, not either full lemma.

One compiler,8GiB Windows Job hard memory,2threads,CPU25%,20min wall timeout.
Whole-project checkpoint180 and whole-project CI status stay unchanged.
Compile included modules in dependency order with pinned lean-toolchain and
lake-manifest, then CheckAxioms.lean. The convenience Linear.lean is not a
newly accepted whole-project checkpoint. Prior archives remain immutable.
