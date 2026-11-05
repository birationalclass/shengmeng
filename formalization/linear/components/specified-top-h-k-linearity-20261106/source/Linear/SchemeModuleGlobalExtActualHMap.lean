module
public import Linear.SchemeModuleCohomologyPointedSource
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- Canonical all-degree map from actual GLOBAL structure-unit Ext to native actual SHEAF H. -/
def schemeModuleGlobalExtActualHMap (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M n →+
      schemeModuleActualCohomology X M n :=
  pointedExactFunctorExtMap (schemeModuleToAdditiveSheaf X)
    (schemeModuleIntegerToUnderlyingUnit X) M n

/-- The SAME actual all-degree comparison map is coefficient-natural. -/
theorem schemeModuleGlobalExtActualHMap_naturality (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M n) :
    schemeModuleGlobalExtActualHMap X N n (x.comp (Ext.mk₀ f) (add_zero n)) =
      CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map f) n
        (schemeModuleGlobalExtActualHMap X M n x) :=
  pointedExactFunctorExtMap_postcompose (schemeModuleToAdditiveSheaf X)
    (schemeModuleIntegerToUnderlyingUnit X) f n x

/-- The comparison uses the SAME actual covariant derived connecting class. -/
theorem schemeModuleGlobalExtActualHMap_boundary (X : Scheme.{u})
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) S.X₃ n) :
    schemeModuleGlobalExtActualHMap X S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (schemeModuleGlobalExtActualHMap X S.X₃ n x).comp
        (schemeModuleShortExact_underlyingAdditiveSheaf S hS).extClass rfl :=
  pointedExactFunctorExtMap_boundary (schemeModuleToAdditiveSheaf X)
    (schemeModuleIntegerToUnderlyingUnit X) hS n x
end LinearStudy
