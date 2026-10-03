module

public import Negativity.CartierEffectivity
public import Negativity.FiniteNormalGeometry
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem birational_functionField_pullback_bijective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : BirationalMorphism f) :
    letI : IsDominant f := birationalMorphism_dominant f hf
    Function.Bijective (dominantFunctionFieldMap f) := by
  let : IsDominant f := birationalMorphism_dominant f hf
  have := birationalMorphism_generic_stalk_isIso f hf
  let g := (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
    f.stalkMap (genericPoint X)
  exact ConcreteCategory.bijective_of_isIso g

/-- Final theorem: on every actual nonempty affine base open, a proper
birational morphism to a normal locally Noetherian integral scheme has
bijective pullback on actual regular functions. The proof uses the actual
function-field isomorphism and actual codimension-one stalk isomorphisms,
then the proved normal-domain extension criterion. It does not assume
proper H^0 finiteness, integral section descent, direct-image equality or
fiber connectedness. This constructs the affine f_*O = O step. -/
theorem proper_normal_birational_affine_functions_bijective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] : Function.Bijective (f.app U) := by
  classical
  let : IsDominant f := birationalMorphism_dominant f hf
  let e : Y.functionField ≃+* X.functionField := RingEquiv.ofBijective
    (dominantFunctionFieldMap f) (birational_functionField_pullback_bijective f hf)
  constructor
  · intro r s hrs
    apply Y.germToFunctionField_injective U
    apply e.injective
    exact (dominantFunctionFieldMap_germ f U r).trans
      ((congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hrs).trans
        (dominantFunctionFieldMap_germ f U s).symm)
  · intro r
    let a := e.symm (X.germToFunctionField (f ⁻¹ᵁ U) r)
    by_cases ha : a = 0
    · refine ⟨0, ?_⟩
      apply X.germToFunctionField_injective (f ⁻¹ᵁ U)
      have he := congrArg e ha
      simpa [a] using he.symm
    · obtain ⟨s, hs⟩ := normal_affine_rational_regular Y hnY U hU (Units.mk0 a ha)
        (by
          intro y hyU hy
          obtain ⟨x, hxy, hi, _hx, _hunique⟩ :=
            proper_birational_codimensionOne_unique_preimage f hf y hy
          subst y
          have : IsIso (f.stalkMap x) := hi
          have := hnY (f x)
          have := normal_codimensionOne_stalk_isDVR Y (f x) hy
          let v := X.presheaf.germ (f ⁻¹ᵁ U) x hyU r
          let t := (inv (f.stalkMap x)).hom v
          have hv : (f.stalkMap x).hom t = v := by
            change ((inv (f.stalkMap x) ≫ f.stalkMap x) v) = v
            simp
          have ht : algebraMap (Y.presheaf.stalk (f x)) Y.functionField t = a := by
            apply e.injective
            change dominantFunctionFieldMap f
              (algebraMap (Y.presheaf.stalk (f x)) Y.functionField t) = e a
            rw [dominantFunctionFieldMap_stalk, hv]
            exact (Scheme.algebraMap_germ_eq_germToFunctionField X hyU r).trans
              (e.apply_symm_apply _).symm
          exact (dvr_rationalOrder_nonneg_iff_regular (Y.presheaf.stalk (f x))
            Y.functionField (Units.mk0 a ha)).mpr ⟨t, ht⟩)
      refine ⟨s, ?_⟩
      apply X.germToFunctionField_injective (f ⁻¹ᵁ U)
      rw [← dominantFunctionFieldMap_germ f U s]
      change e (algebraMap Γ(Y, U) Y.functionField s) = _
      rw [hs]
      exact e.apply_symm_apply _

end
end Negativity
