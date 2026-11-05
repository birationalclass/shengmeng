module
public import Linear.OriginalDegreeVeroneseAffineOverlap
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
local instance originalDegreeVeroneseOverlapProjectionGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q

@[reassoc]
theorem originalDegreeVeroneseAmbientOverlap_inv_fst (i j : I) :
    (originalDegreeVeroneseAmbientOverlap B q i j).inv ≫
        pullback.fst ((C).f i) ((C).f j) =
      Spec.map (originalDegreeVeroneseBundledAmbientRes B q
        (f := i.2.1) (g := j.2.1) (x := i.2.1 * j.2.1) j.2.2 rfl) :=
  Proj.pullbackAwayιIso_inv_fst B
    (f := (i.2.1 : S)) (g := (j.2.1 : S))
    (m := q * (i.1 : ℕ)) (m' := q * (j.1 : ℕ))
    i.2.2 (Nat.mul_pos hq.out i.1.2) j.2.2 (Nat.mul_pos hq.out j.1.2) rfl

@[reassoc]
theorem originalDegreeVeroneseAmbientOverlap_inv_snd (i j : I) :
    (originalDegreeVeroneseAmbientOverlap B q i j).inv ≫
        pullback.snd ((C).f i) ((C).f j) =
      Spec.map (originalDegreeVeroneseBundledAmbientRes B q
        (f := j.2.1) (g := i.2.1) (x := i.2.1 * j.2.1) i.2.2 (mul_comm _ _)) :=
  Proj.pullbackAwayιIso_inv_snd B
    (f := (i.2.1 : S)) (g := (j.2.1 : S))
    (m := q * (i.1 : ℕ)) (m' := q * (j.1 : ℕ))
    i.2.2 (Nat.mul_pos hq.out i.1.2) j.2.2 (Nat.mul_pos hq.out j.1.2) rfl

@[reassoc]
theorem originalDegreeVeroneseRegradedOverlap_inv_fst (i j : I) :
    (originalDegreeVeroneseRegradedOverlap B q i j).inv ≫
        pullback.fst ((D).f i) ((D).f j) =
      Spec.map (originalDegreeVeroneseBundledChartRes B q
        (f := i.2.1) (g := j.2.1) (x := i.2.1 * j.2.1) j.2.2 rfl) :=
  Proj.pullbackAwayιIso_inv_fst P (f := i.2.1) (g := j.2.1)
    i.2.2 i.1.2 j.2.2 j.1.2 rfl

@[reassoc]
theorem originalDegreeVeroneseRegradedOverlap_inv_snd (i j : I) :
    (originalDegreeVeroneseRegradedOverlap B q i j).inv ≫
        pullback.snd ((D).f i) ((D).f j) =
      Spec.map (originalDegreeVeroneseBundledChartRes B q
        (f := j.2.1) (g := i.2.1) (x := i.2.1 * j.2.1) i.2.2 (mul_comm _ _)) :=
  Proj.pullbackAwayιIso_inv_snd P (f := i.2.1) (g := j.2.1)
    i.2.2 i.1.2 j.2.2 j.1.2 rfl

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_fst
#print axioms LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_fst
#check LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_snd
#print axioms LinearStudy.originalDegreeVeroneseAmbientOverlap_inv_snd
#check LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_fst
#print axioms LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_fst
#check LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_snd
#print axioms LinearStudy.originalDegreeVeroneseRegradedOverlap_inv_snd

