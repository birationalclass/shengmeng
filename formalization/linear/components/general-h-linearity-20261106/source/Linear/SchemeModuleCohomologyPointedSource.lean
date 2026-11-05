module
public import Linear.SchemeModuleInjectiveActualCohomology
public import Linear.TopAbelianSheafIntegerSections
public import Linear.PointedExactFunctorExtMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- The actual scheme-module forgetful functor is additive. -/
@[instance] theorem schemeModuleToAdditiveSheaf_additive (X : Scheme.{u}) :
    (schemeModuleToAdditiveSheaf X).Additive where
  map_add := by intros; rfl

/-- The actual underlying-sheaf functor preserves finite colimits. -/
@[instance] theorem schemeModuleToAdditiveSheaf_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (schemeModuleToAdditiveSheaf X) := by
  letI : PreservesColimitsOfSize.{u,u} (schemeModuleToAdditiveSheaf X) :=
    schemeModuleAdditiveSheaf_preservesColimitsOfSize X
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The original integer SHEAF maps to the actual underlying structure unit by its global section1. -/
def schemeModuleIntegerToUnderlyingUnit (X : Scheme.{u}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
        (schemeModuleToAdditiveSheaf X).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (topAbelianSheafIntegerHomSectionsAddEquiv X
    ((schemeModuleToAdditiveSheaf X).obj (SheafOfModules.unit X.ringCatSheaf))).symm
      (1 : Γ(X,⊤))

/-- The SAME original source morphism has precisely the actual global section1. -/
theorem schemeModuleIntegerToUnderlyingUnit_section (X : Scheme.{u}) :
    topAbelianSheafIntegerHomSectionsAddEquiv X
      ((schemeModuleToAdditiveSheaf X).obj (SheafOfModules.unit X.ringCatSheaf))
      (schemeModuleIntegerToUnderlyingUnit X) = (1 : Γ(X,⊤)) :=
  (topAbelianSheafIntegerHomSectionsAddEquiv X
    ((schemeModuleToAdditiveSheaf X).obj (SheafOfModules.unit X.ringCatSheaf))).apply_symm_apply _
end LinearStudy
