module
public import Linear.SchemeModuleActualCohomologyGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- A nonzero original additive functional represented by actual H of a
coefficient morphism forces that SAME actual morphism to be nonzero.
This does not construct a representative or assume geometric duality. -/
theorem schemeModuleActualTraceRepresentingMap_ne_zero
    {K : Type u} [AddCommGroup K] (X : Scheme.{u}) {M W : X.Modules} (r : ℕ)
    (trace : schemeModuleActualCohomology X W r →+ K)
    (ell : schemeModuleActualCohomology X M r →+ K) (hell : ell ≠ 0)
    (a : M ⟶ W) (hrep : ∀ x, trace (CategoryTheory.Sheaf.H.map
      ((schemeModuleToActualAbelianSheaf X).map a) r x)=ell x) : a ≠ 0 := by
  intro ha
  apply hell
  apply AddMonoidHom.ext
  intro x
  have h := hrep x
  rw [ha] at h
  have hz : (schemeModuleToActualAbelianSheaf X).map (0 : M ⟶ W)=0 := by
    change (SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ W)=0
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero M W
  rw [hz] at h
  simpa only [CategoryTheory.Sheaf.H.map_apply,Ext.mk₀_zero,Ext.comp_zero,map_zero,AddMonoidHom.zero_apply] using h.symm
end LinearStudy
