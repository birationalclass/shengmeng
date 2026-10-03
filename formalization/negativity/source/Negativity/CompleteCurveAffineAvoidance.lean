module

public import Negativity.CurveFunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem complete_integral_curve_not_affine
    (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
    (k : Type u) [Field k] (c : C ⟶ Spec (.of k)) [IsProper c] : ¬ IsAffine C := by
  intro ha
  have := ha
  have hfield := isField_of_universallyClosed k c
  obtain ⟨x, hx⟩ := curve_exists_coheight_one C hd
  let p := C.isoSpec.hom x
  have hle := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
  rw [ringKrullDim_eq_zero_of_isField hfield] at hle
  change (↑(C.isoSpec.hom x).asIdeal.height : WithBot ℕ∞) ≤ 0 at hle
  rw [idealHeight_eq_coheight, coheight_eq_of_isOpenImmersion, hx] at hle
  norm_num at hle

/-- Final theorem: an actual closed complete integral curve cannot be
contained in an affine open of the ambient scheme. The contradiction is
geometric: its closed factorization would make the proper curve affine,
whose global coordinate ring is a field and hence has dimension zero. -/
theorem complete_integral_curve_meets_complement_affine_open
    {C X : Scheme.{u}} [IsIntegral C] (hd : Order.krullDim C = 1)
    (k : Type u) [Field k] (c : C ⟶ Spec (.of k)) [IsProper c]
    (j : C ⟶ X) [IsClosedImmersion j]
    (U : X.Opens) (hU : IsAffineOpen U) : ∃ x : C, j x ∉ U := by
  classical
  by_contra! hall
  have hrange : Set.range j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hall x
  let l : C ⟶ U.toScheme := IsOpenImmersion.lift U.ι j hrange
  have hl : l ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ hrange
  have : IsClosedImmersion (l ≫ U.ι) := by rw [hl]; infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l U.ι
  have : IsAffine U.toScheme := hU
  have : IsAffine C := isAffine_of_isAffineHom l
  exact complete_integral_curve_not_affine C hd k c inferInstance

end
end Negativity
