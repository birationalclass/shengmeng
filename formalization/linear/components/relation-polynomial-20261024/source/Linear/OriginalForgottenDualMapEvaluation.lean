module
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
variable {K : Type} [Field K]
/-- Actual value of the ORIGINAL canonical scalar-forgetting map on
an ORIGINAL linear dual map. Both ModuleCat objects stay explicit. -/
theorem originalForgottenModuleDualMap_apply
    (V W : ModuleCat K) (p : V ⟶ W) (ell : Module.Dual K W) (v : V) :
    (show Module.Dual K V from
      ((forget₂ (ModuleCat K) AddCommGrpCat).map
        (ModuleCat.ofHom (p.hom.dualMap))) ell) v = ell (p.hom v) := by
  rfl
/-- Same original map,with ORIGINAL coefficient types and linear map.
This is a calibrated value identity,not a geometric trace identification. -/
theorem originalForgottenLinearDualMap_apply
    {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : V →ₗ[K] W) (ell : Module.Dual K W) (v : V) :
    (show Module.Dual K V from
      ((forget₂ (ModuleCat K) AddCommGrpCat).map
        (ModuleCat.ofHom (p.dualMap))) ell) v = ell (p v) := by
  rfl
/-- Evaluation of a PROVED original coefficient square. The square is
an explicit premise of this generic transfer,not claimed proved here.
Its application to the old specified top comparison remains separate. -/
theorem originalSpecifiedEvaluationPairing_of_coefficientSquare
    {H H' : AddCommGrpCat} (V W : ModuleCat K)
    (I : H ≅ (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K (Module.Dual K W)))
    (J : H' ≅ (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K (Module.Dual K V)))
    (u : H ⟶ H') (p : V ⟶ W)
    (square : u ≫ J.hom = I.hom ≫
      (forget₂ (ModuleCat K) AddCommGrpCat).map (ModuleCat.ofHom (p.hom.dualMap)))
    (x : H) (v : V) :
    (show Module.Dual K V from J.hom (u x)) v =
      (show Module.Dual K W from I.hom x) (p.hom v) := by
  have hx := congrArg (fun g : H ⟶
      (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K (Module.Dual K V)) =>
    (show Module.Dual K V from g x) v) square
  simp only [AddCommGrpCat.comp_apply] at hx
  exact hx
end LinearStudy
