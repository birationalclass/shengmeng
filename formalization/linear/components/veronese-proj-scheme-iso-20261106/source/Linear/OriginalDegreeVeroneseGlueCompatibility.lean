module
public import Linear.OriginalDegreeVeroneseAffineOverlapIso
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
local instance originalDegreeVeroneseGlueCompatibilityGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q
local notation "E" => originalDegreeVeroneseIndexedAffineIso B q
local notation "O" => originalDegreeVeroneseAffineOverlapIso B q

private theorem inverseProjection
    {W W' T T' : Scheme.{v}} (e : W ≅ W') (j : T ≅ T')
    (p : W ⟶ T) (r : W' ⟶ T') (h : e.hom ≫ r = p ≫ j.hom) :
    e.inv ≫ p = r ≫ j.inv := by
  rw [← cancel_mono j.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.inv_hom_id_assoc]

@[reassoc]
theorem originalDegreeVeroneseAffineOverlapIso_inv_fst (i j : I) :
    (O i j).inv ≫ pullback.fst ((C).f i) ((C).f j) =
      pullback.fst ((D).f i) ((D).f j) ≫ (E i).inv :=
  inverseProjection (O i j) (E i) _ _
    (originalDegreeVeroneseAffineOverlapIso_hom_fst B q i j)

@[reassoc]
theorem originalDegreeVeroneseAffineOverlapIso_inv_snd (i j : I) :
    (O i j).inv ≫ pullback.snd ((C).f i) ((C).f j) =
      pullback.snd ((D).f i) ((D).f j) ≫ (E j).inv :=
  inverseProjection (O i j) (E j) _ _
    (originalDegreeVeroneseAffineOverlapIso_hom_snd B q i j)

/-- The chart maps from the original Proj agree on the actual intersections. -/
theorem originalDegreeVeroneseForwardChartCompatibility (i j : I) :
    pullback.fst ((C).f i) ((C).f j) ≫ (E i).hom ≫ (D).f i =
      pullback.snd ((C).f i) ((C).f j) ≫ (E j).hom ≫ (D).f j := by
  rw [← originalDegreeVeroneseAffineOverlapIso_hom_fst_assoc B q i j,
    ← originalDegreeVeroneseAffineOverlapIso_hom_snd_assoc B q i j, pullback.condition]

/-- The inverse chart maps agree on the actual intersections. -/
theorem originalDegreeVeroneseInverseChartCompatibility (i j : I) :
    pullback.fst ((D).f i) ((D).f j) ≫ (E i).inv ≫ (C).f i =
      pullback.snd ((D).f i) ((D).f j) ≫ (E j).inv ≫ (C).f j := by
  rw [← originalDegreeVeroneseAffineOverlapIso_inv_fst_assoc B q i j,
    ← originalDegreeVeroneseAffineOverlapIso_inv_snd_assoc B q i j, pullback.condition]

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_fst
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_fst
#check LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_snd
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_inv_snd
#check LinearStudy.originalDegreeVeroneseForwardChartCompatibility
#print axioms LinearStudy.originalDegreeVeroneseForwardChartCompatibility
#check LinearStudy.originalDegreeVeroneseInverseChartCompatibility
#print axioms LinearStudy.originalDegreeVeroneseInverseChartCompatibility

