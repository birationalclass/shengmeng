module
public import Linear.SchemeModuleGlobalExtActualHMap
public import Linear.PointedExactFunctorExtZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe u
/-- The canonical derived map in degree zero is exactly the previously verified evaluation-at1 map. -/
theorem schemeModuleGlobalExtActualHMap_zero (X : Scheme.{u}) (M : X.Modules)
    (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M 0) :
    schemeModuleGlobalExtActualHMap X M 0 x = schemeModuleGlobalExtZeroActualHAddEquiv X M x := by
  apply (CategoryTheory.Sheaf.H.equiv₀ ((schemeModuleToActualAbelianSheaf X).obj M)
    isTerminalTop).injective
  calc
    _ = topAbelianSheafIntegerHomSectionsAddEquiv X
        ((schemeModuleToAdditiveSheaf X).obj M)
        (Ext.addEquiv₀ (schemeModuleGlobalExtActualHMap X M 0 x)) := rfl
    _ = topAbelianSheafIntegerHomSectionsAddEquiv X
        ((schemeModuleToAdditiveSheaf X).obj M)
        (schemeModuleIntegerToUnderlyingUnit X ≫
          (schemeModuleToAdditiveSheaf X).map (Ext.addEquiv₀ x)) :=
      congrArg (topAbelianSheafIntegerHomSectionsAddEquiv X
        ((schemeModuleToAdditiveSheaf X).obj M))
        (pointedExactFunctorExtMap_zero_homEquiv (schemeModuleToAdditiveSheaf X)
          (schemeModuleIntegerToUnderlyingUnit X) M x)
    _ = ((schemeModuleToAdditiveSheaf X).map (Ext.addEquiv₀ x)).hom.app (op ⊤)
        (topAbelianSheafIntegerHomSectionsAddEquiv X
          ((schemeModuleToAdditiveSheaf X).obj (SheafOfModules.unit X.ringCatSheaf))
          (schemeModuleIntegerToUnderlyingUnit X)) :=
      topAbelianSheafIntegerHomSectionsAddEquiv_postcompose X
        ((schemeModuleToAdditiveSheaf X).map (Ext.addEquiv₀ x))
        (schemeModuleIntegerToUnderlyingUnit X)
    _ = Scheme.Modules.Hom.app (Ext.addEquiv₀ x) ⊤ (1 : Γ(X,⊤)) :=
      congrArg (((schemeModuleToAdditiveSheaf X).map (Ext.addEquiv₀ x)).hom.app (op ⊤))
        (schemeModuleIntegerToUnderlyingUnit_section X)
    _ = _ := (schemeModuleGlobalExtZeroActualHAddEquiv_evaluate X M x).symm
end LinearStudy
