module
public import Linear.SchemeModuleInternalExtSourceAdditive
public import Linear.SchemeModuleUnitInternalExt
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Positive ACTUAL derived SHEAF Ext from every ACTUAL finite free module
sheaf vanishes for EVERY actual coefficient. Reuse native free coproduct,
opposite-limit duality and PROVED source additivity/unit vanishing.
No global projectivity of free sheaves is asserted. -/
theorem schemeModuleFiniteFreeInternalExt_succ (N : X.Modules) (ι : Type u) [Finite ι]
    (q : ℕ) :
    IsZero (schemeModuleInternalExt
      (SheafOfModules.free (R := X.ringCatSheaf) ι) N (q+1)) := by
  let F := schemeModuleInternalExtSourceFunctor X N (q+1)
  letI : F.Additive := schemeModuleInternalExtSourceFunctor_additive X N (q+1)
  letI : PreservesLimitsOfShape (Discrete ι)ᵒᵖ F :=
    preservesLimitsOfShape_of_equiv (Discrete.opposite ι).symm F
  let D : Discrete ι ⥤ X.Modules :=
    Discrete.functor (fun _ => SheafOfModules.unit X.ringCatSheaf)
  let c : Cocone D := SheafOfModules.freeCofan (R := X.ringCatSheaf) ι
  have hc : IsColimit c := SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) ι
  have hF : IsZero (D.op ⋙ F) :=
    (D.op ⋙ F).isZero_iff.2 (fun _ => schemeModuleUnitInternalExt_succ N q)
  exact (isLimitOfPreserves F hc.op).isZero_pt hF

end LinearStudy
