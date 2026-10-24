module
public import Linear.CoextensionEvaluationAtOne
public import Linear.FiniteCoextensionUpperModule
public import Linear.FiniteCoextensionTorsionFree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- The ORIGINAL K and R actions on the SAME coextension form a tower.
Both are restrictions of its ORIGINAL S action; no action is transported. -/
theorem coextensionOriginalBaseScalarTower :
    IsScalarTower K R
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a ell
  change algebraMap R S (algebraMap K R a) • ell = algebraMap K S a • ell
  rw [← IsScalarTower.algebraMap_apply K R S]
/-- Torsion freeness required by the SAME top duality is DERIVED from
finite domain extension and the original coextension action. -/
theorem coextensionOriginalTopDualityTorsionFree [IsDomain R] [IsDomain S]
    [Module.Finite R S] :
    Module.IsTorsionFree S
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
  letI : Algebra.IsAlgebraic R S := inferInstance
  exact Module.IsTorsionFree.of_smul_eq_zero
    (coextension_smul_eq_zero (R:=R) (S:=S))
end LinearStudy
