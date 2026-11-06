module
public import Linear.OriginalDegreeVeroneseAffineCover
public import Mathlib.AlgebraicGeometry.Pullbacks
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseAffineOverlapGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q

/-- The local isomorphism on each pair of equally indexed affine charts. -/
def originalDegreeVeroneseIndexedAffineIso (i : I) :
    Spec ((C).X i) ≅ Spec ((D).X i) :=
  originalDegreeVeroneseSpecChartIso B q i.2.2

/-- An intersection of two original charts is the original product chart. -/
def originalDegreeVeroneseAmbientOverlap (i j : I) :
    pullback ((C).f i) ((C).f j) ≅
      Spec (originalDegreeVeroneseBundledAmbientChart B q (i.2.1 * j.2.1)) :=
  Proj.pullbackAwayιIso B
    (f := (i.2.1 : S)) (g := (j.2.1 : S))
    (m := q * (i.1 : ℕ)) (m' := q * (j.1 : ℕ))
    i.2.2 (Nat.mul_pos hq.out i.1.2) j.2.2 (Nat.mul_pos hq.out j.1.2) rfl

/-- An intersection of two regraded charts is the regraded product chart. -/
def originalDegreeVeroneseRegradedOverlap (i j : I) :
    pullback ((D).f i) ((D).f j) ≅
      Spec (originalDegreeVeroneseBundledChart B q (i.2.1 * j.2.1)) :=
  Proj.pullbackAwayιIso P (f := i.2.1) (g := j.2.1)
    i.2.2 i.1.2 j.2.2 j.1.2 rfl

end LinearStudy
#check LinearStudy.originalDegreeVeroneseIndexedAffineIso
#print axioms LinearStudy.originalDegreeVeroneseIndexedAffineIso
#check LinearStudy.originalDegreeVeroneseAmbientOverlap
#print axioms LinearStudy.originalDegreeVeroneseAmbientOverlap
#check LinearStudy.originalDegreeVeroneseRegradedOverlap
#print axioms LinearStudy.originalDegreeVeroneseRegradedOverlap

