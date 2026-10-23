module
public import Linear.SchemeModuleActualCohomologyGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- A GENERIC logical transfer for ORIGINAL actual H and actual sheaf maps.
It takes explicit trace separation;the coextension application supplies it
from the newly PROVED original adjunction,not as an extra hypothesis. -/
theorem schemeModuleActualTraceSeparation_vanish_of_hom_zero
    {K : Type u} [AddCommGroup K] (X : Scheme.{u}) (M W : X.Modules) (r : ℕ)
    (trace : schemeModuleActualCohomology X W r →+ K)
    (hsep : ∀ x : schemeModuleActualCohomology X M r,
      (∀ a : M ⟶ W,trace (CategoryTheory.Sheaf.H.map
        ((schemeModuleToActualAbelianSheaf X).map a) r x)=0) → x=0)
    (hhom : ∀ a : M ⟶ W,a=0) :
    Subsingleton (schemeModuleActualCohomology X M r) := by
  have hz : ∀ x : schemeModuleActualCohomology X M r,x=0 := by
    intro x
    apply hsep x
    intro a
    rw [hhom a]
    have ha : (schemeModuleToActualAbelianSheaf X).map (0 : M ⟶ W) = 0 := by
      change (SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ W)=0
      exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero M W
    rw [ha]
    simp only [CategoryTheory.Sheaf.H.map_apply,Ext.mk₀_zero,Ext.comp_zero,map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩
end LinearStudy
