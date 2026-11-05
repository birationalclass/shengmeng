module
public import Linear.OriginalDegreeVeroneseOverlapProjection
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
local instance originalDegreeVeroneseOverlapIsoGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q

private theorem overlapIso_projection
    {A A' Z Z' T U : Scheme.{v}}
    (a : A ≅ A') (b : Z ≅ Z') (e : A' ≅ Z') (j : T ≅ U)
    (p : A ⟶ T) (r : Z ⟶ U)
    (h : (a.inv ≫ p) ≫ j.hom = e.hom ≫ (b.inv ≫ r)) :
    (a ≪≫ e ≪≫ b.symm).hom ≫ r = p ≫ j.hom := by
  rw [← cancel_epi a.inv]
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using h.symm

/-- The comparison on the actual intersection of two affine charts. -/
def originalDegreeVeroneseAffineOverlapIso (i j : I) :
    pullback ((C).f i) ((C).f j) ≅ pullback ((D).f i) ((D).f j) :=
  originalDegreeVeroneseAmbientOverlap B q i j ≪≫
    originalDegreeVeroneseSpecChartIso B q (SetLike.mul_mem_graded i.2.2 j.2.2) ≪≫
    (originalDegreeVeroneseRegradedOverlap B q i j).symm

@[reassoc]
theorem originalDegreeVeroneseAffineOverlapIso_hom_fst (i j : I) :
    (originalDegreeVeroneseAffineOverlapIso B q i j).hom ≫
        pullback.fst ((D).f i) ((D).f j) =
      pullback.fst ((C).f i) ((C).f j) ≫ (originalDegreeVeroneseIndexedAffineIso B q i).hom := by
  apply overlapIso_projection
  rw [originalDegreeVeroneseAmbientOverlap_inv_fst, originalDegreeVeroneseRegradedOverlap_inv_fst]
  exact originalDegreeVeroneseSpecChartSquare B q i.2.2 j.2.2 rfl rfl
    (SetLike.mul_mem_graded i.2.2 j.2.2)

@[reassoc]
theorem originalDegreeVeroneseAffineOverlapIso_hom_snd (i j : I) :
    (originalDegreeVeroneseAffineOverlapIso B q i j).hom ≫
        pullback.snd ((D).f i) ((D).f j) =
      pullback.snd ((C).f i) ((C).f j) ≫ (originalDegreeVeroneseIndexedAffineIso B q j).hom := by
  apply overlapIso_projection
  rw [originalDegreeVeroneseAmbientOverlap_inv_snd, originalDegreeVeroneseRegradedOverlap_inv_snd]
  have h : i.2.1 * j.2.1 ∈ P ((j.1 : ℕ) + (i.1 : ℕ)) :=
    (mul_comm _ _ : i.2.1 * j.2.1 = j.2.1 * i.2.1).symm ▸ SetLike.mul_mem_graded j.2.2 i.2.2
  exact originalDegreeVeroneseSpecChartSquare B q j.2.2 i.2.2 (mul_comm _ _) (mul_comm _ _) h

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAffineOverlapIso
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso
#check LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_fst
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_fst
#check LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_snd
#print axioms LinearStudy.originalDegreeVeroneseAffineOverlapIso_hom_snd

