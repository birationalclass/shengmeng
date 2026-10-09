module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace LinearStudy
open CategoryTheory
universe u v₁ u₁
variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting free generators through a real sheaf isomorphism gives
an isomorphism as presentation map; this keeps the large native Proj
construction opaque when the actual local trivializations are applied. -/
theorem freeIsoGeneratingSections_isIso {M : SheafOfModules.{u} R}
    {I : Type u} (e : SheafOfModules.free (R := R) I ≅ M) :
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi e.hom).π := by
  erw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π, Category.id_comp]
  infer_instance

end LinearStudy
