module

public import Negativity.FiniteNormalGeometry
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the actual generic-field maps of dominant Scheme
morphisms compose. This identifies the field degree on a constructed
normalization with the degree of the original curve map. -/
theorem dominantFunctionFieldMap_comp {C Y X : Scheme}
    [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (g : C ⟶ Y) (f : Y ⟶ X) [IsDominant g] [IsDominant f] :
    dominantFunctionFieldMap (g ≫ f) =
      (dominantFunctionFieldMap g).comp (dominantFunctionFieldMap f) := by
  obtain ⟨U, hU, hη, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint X) trivial
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint Y, by
    change f (genericPoint Y) ∈ U
    rw [dominant_genericPoint_eq f]
    exact hη⟩⟩
  have : Nonempty (g ⁻¹ᵁ f ⁻¹ᵁ U) := ⟨⟨genericPoint C, by
    change f (g (genericPoint C)) ∈ U
    rw [dominant_genericPoint_eq g, dominant_genericPoint_eq f]
    exact hη⟩⟩
  have : Nonempty ((g ≫ f) ⁻¹ᵁ U) := by
    simpa only [Scheme.Hom.comp_preimage] using ‹Nonempty (g ⁻¹ᵁ f ⁻¹ᵁ U)›
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply IsLocalization.ringHom_ext (Γ(X, U))⁰
  ext a
  change dominantFunctionFieldMap (g ≫ f) (X.germToFunctionField U a) =
    dominantFunctionFieldMap g (dominantFunctionFieldMap f (X.germToFunctionField U a))
  rw [dominantFunctionFieldMap_germ (g ≫ f), dominantFunctionFieldMap_germ f,
    dominantFunctionFieldMap_germ g]
  rw [Scheme.Hom.comp_app]
  rfl

end
end Negativity
