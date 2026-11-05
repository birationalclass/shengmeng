module
public import Linear.OriginalDegreeVeroneseProjGlue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseProjIsoGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q
local notation "E" => originalDegreeVeroneseIndexedAffineIso B q
local notation "F" => originalDegreeVeroneseProjHom B q
local notation "G" => originalDegreeVeroneseProjInv B q

theorem originalDegreeVeroneseProjHom_comp_Inv : F ≫ G = 𝟙 (Proj B) := by
  apply (C).openCover.hom_ext
  intro i
  change (C).f i ≫ F ≫ G = (C).f i ≫ 𝟙 (Proj B)
  rw [originalDegreeVeroneseProjHom_onChart_assoc B q i,
    originalDegreeVeroneseProjInv_onChart B q i, Iso.hom_inv_id_assoc, Category.comp_id]

theorem originalDegreeVeroneseProjInv_comp_Hom : G ≫ F = 𝟙 (Proj P) := by
  apply (D).openCover.hom_ext
  intro i
  change (D).f i ≫ G ≫ F = (D).f i ≫ 𝟙 (Proj P)
  rw [originalDegreeVeroneseProjInv_onChart_assoc B q i,
    originalDegreeVeroneseProjHom_onChart B q i, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The original Proj and the degree-q Veronese Proj are isomorphic
as schemes via the exact common chart fraction maps. -/
def originalDegreeVeroneseProjIso : Proj B ≅ Proj P where
  hom := F
  inv := G
  hom_inv_id := originalDegreeVeroneseProjHom_comp_Inv B q
  inv_hom_id := originalDegreeVeroneseProjInv_comp_Hom B q

@[reassoc]
theorem originalDegreeVeroneseProjIso_hom_onChart (i : I) :
    (C).f i ≫ (originalDegreeVeroneseProjIso B q).hom = (E i).hom ≫ (D).f i :=
  originalDegreeVeroneseProjHom_onChart B q i

@[reassoc]
theorem originalDegreeVeroneseProjIso_inv_onChart (i : I) :
    (D).f i ≫ (originalDegreeVeroneseProjIso B q).inv = (E i).inv ≫ (C).f i :=
  originalDegreeVeroneseProjInv_onChart B q i

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProjHom_comp_Inv
#print axioms LinearStudy.originalDegreeVeroneseProjHom_comp_Inv
#check LinearStudy.originalDegreeVeroneseProjInv_comp_Hom
#print axioms LinearStudy.originalDegreeVeroneseProjInv_comp_Hom
#check LinearStudy.originalDegreeVeroneseProjIso
#print axioms LinearStudy.originalDegreeVeroneseProjIso
#check LinearStudy.originalDegreeVeroneseProjIso_hom_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjIso_hom_onChart
#check LinearStudy.originalDegreeVeroneseProjIso_inv_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjIso_inv_onChart

