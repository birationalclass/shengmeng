module
public import Linear.SchemeModuleInternalExtSupportedUnit
public import Linear.SchemeModuleGlobalToInternalExtAllDegrees
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
/-- Actual open restriction detects vanishing of an actual GLOBAL Ext
class when the SAME canonical lambda is injective and the ACTUAL
internal-Ext target restriction unit is iso. Original finite-cut
geometry derives BOTH hypotheses independently of the desired class. -/
theorem schemeModuleGlobalExt_zero_iff_open
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (E N : X.Modules) (p : ℕ)
    (hi : Function.Injective (schemeModuleGlobalToInternalExt E N p))
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app
      (schemeModuleInternalExt E N (p+1))))
    (x : Ext.{u} E N (p+1)) :
    x = 0 ↔ (Scheme.Modules.restrictFunctor j).map
      (schemeModuleGlobalToInternalExtAll E N (p+1) x) = 0 := by
  rw [schemeModuleGlobalToInternalExtAll_succ]
  constructor
  · intro hx
    rw [hx,map_zero,Functor.map_zero]
  · intro hx
    apply hi
    rw [map_zero]
    exact (schemeModule_morphism_zero_iff_restrict_of_target_unit_isIso j
      (schemeModuleGlobalToInternalExt E N p x) hu).mpr hx
end LinearStudy
