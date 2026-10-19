module
public import Linear.SchemeModuleInternalExtSourceAdditive
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

/-- SAME actual derived SHEAF Ext vanishing is preserved by a FINITE
biproduct of sources. Reuse proved source additivity and native limits. -/
theorem schemeModuleBiproductInternalExt_isZero (N : X.Modules) {ι : Type u}
    [Fintype ι] (P : ι → X.Modules) [HasBiproduct P] (q : ℕ)
    (hP : ∀ i, IsZero (schemeModuleInternalExt (P i) N q)) :
    IsZero (schemeModuleInternalExt (biproduct P) N q) := by
  let F := schemeModuleInternalExtSourceFunctor X N q
  letI : F.Additive := schemeModuleInternalExtSourceFunctor_additive X N q
  letI : PreservesLimitsOfShape (Discrete ι)ᵒᵖ F :=
    preservesLimitsOfShape_of_equiv (Discrete.opposite ι).symm F
  let D : Discrete ι ⥤ X.Modules := Discrete.functor P
  have hF : IsZero (D.op ⋙ F) := (D.op ⋙ F).isZero_iff.2 (fun i => hP i.unop.as)
  exact (isLimitOfPreserves F (biproduct.isColimit P).op).isZero_pt hF

end LinearStudy
