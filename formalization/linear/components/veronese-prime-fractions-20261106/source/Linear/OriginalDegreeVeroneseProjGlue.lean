module
public import Linear.OriginalDegreeVeroneseGlueCompatibility
public import Mathlib.AlgebraicGeometry.Gluing
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
local instance originalDegreeVeroneseProjGlueGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

local notation "I" => OriginalDegreeVeroneseChartIndex B q
local notation "C" => originalDegreeVeroneseAmbientAffineCover B q
local notation "D" => originalDegreeVeroneseRegradedAffineCover B q
local notation "E" => originalDegreeVeroneseIndexedAffineIso B q

/-- Glue the original-to-Veronese maps on the common affine cover. -/
def originalDegreeVeroneseProjHom : Proj B ⟶ Proj P :=
  (C).openCover.glueMorphisms
    (fun i => (E i).hom ≫ (D).f i)
    (originalDegreeVeroneseForwardChartCompatibility B q)

/-- Glue the Veronese-to-original maps on the common affine cover. -/
def originalDegreeVeroneseProjInv : Proj P ⟶ Proj B :=
  (D).openCover.glueMorphisms
    (fun i => (E i).inv ≫ (C).f i)
    (originalDegreeVeroneseInverseChartCompatibility B q)

@[reassoc]
theorem originalDegreeVeroneseProjHom_onChart (i : I) :
    (C).f i ≫ originalDegreeVeroneseProjHom B q =
      (E i).hom ≫ (D).f i :=
  (C).openCover.ι_glueMorphisms _ _ i

@[reassoc]
theorem originalDegreeVeroneseProjInv_onChart (i : I) :
    (D).f i ≫ originalDegreeVeroneseProjInv B q =
      (E i).inv ≫ (C).f i :=
  (D).openCover.ι_glueMorphisms _ _ i

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProjHom
#print axioms LinearStudy.originalDegreeVeroneseProjHom
#check LinearStudy.originalDegreeVeroneseProjInv
#print axioms LinearStudy.originalDegreeVeroneseProjInv
#check LinearStudy.originalDegreeVeroneseProjHom_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjHom_onChart
#check LinearStudy.originalDegreeVeroneseProjInv_onChart
#print axioms LinearStudy.originalDegreeVeroneseProjInv_onChart

