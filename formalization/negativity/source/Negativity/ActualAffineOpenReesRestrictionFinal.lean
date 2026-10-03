module
public import Negativity.ActualAffineOpenReesBaseScalars
public import Negativity.ActualAffineOpenReesRestriction
public import Negativity.ReesRestrictionGenerators
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual affine image coordinates respect the actual base pullback to the chart. -/
theorem actual_affine_open_rees_sections_base_scalars_appLE (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) (p : reesAlgebra I) :
    let := actualAffineOpenCoefficientAlgebra f U
    actualAffineOpenReesSectionsEquiv f I U hU
      ((actualRelativeReesToBase f I).appLE ⊤ (actualRelativeReesToSource f I ⁻¹ᵁ U) le_top
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)) =
      actualReesCoefficientMap (S := Γ(X,U)) I p := by
  let := actualAffineOpenCoefficientAlgebra f U
  have hr := ConcreteCategory.congr_hom
    (actual_appTop_restriction (actualRelativeReesToBase f I)
      (actualRelativeReesToSource f I ⁻¹ᵁ U))
    ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)
  change actualSectionRestriction (actualRelativeReesScheme f I) le_top
    ((actualRelativeReesToBase f I).appTop _) =
      (actualRelativeReesToBase f I).appLE ⊤ _ le_top _ at hr
  rw [← hr]
  exact actual_affine_open_rees_sections_base_scalars f I U hU p

/-- The inverse chart coordinates recover every actual base Rees scalar. -/
theorem actual_affine_open_rees_sections_symm_base_scalars (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) (p : reesAlgebra I) :
    let := actualAffineOpenCoefficientAlgebra f U
    (actualAffineOpenReesSectionsEquiv f I U hU).symm
      (actualReesCoefficientMap (S := Γ(X,U)) I p) =
      (actualRelativeReesToBase f I).appLE ⊤ (actualRelativeReesToSource f I ⁻¹ᵁ U) le_top
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p) := by
  let := actualAffineOpenCoefficientAlgebra f U
  exact actual_ring_equiv_symm_of_apply _ _ _
    (actual_affine_open_rees_sections_base_scalars_appLE f I U hU p)

/-- The actual original Rees generators restrict by coefficientwise source restriction. -/
theorem actual_affine_open_rees_restriction_base_scalars (f : X ⟶ Spec (.of R))
    (I : Ideal R) {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (p : reesAlgebra I) :
    let := actualAffineOpenCoefficientAlgebra f U
    (actualAffineOpenReesSectionsEquiv f I V hV
      (actualReesOpenSectionsRestriction f I h
        ((actualAffineOpenReesSectionsEquiv f I U hU).symm
          (actualReesCoefficientMap (S := Γ(X,U)) I p)))).1 =
      (actualReesCoefficientMap (S := Γ(X,U)) I p).1.map (actualOpenSectionsRestriction h) := by
  let := actualAffineOpenCoefficientAlgebra f U
  let := actualAffineOpenCoefficientAlgebra f V
  dsimp only
  rw [actual_affine_open_rees_sections_symm_base_scalars,
    actual_rees_sections_restrict_base, actual_affine_open_rees_sections_base_scalars_appLE]
  exact actual_rees_coefficient_map_restriction f I h p

/-- Genuine section restrictions on the actual relative Rees closed image become
coefficientwise polynomial restrictions under the proved actual affine-open coordinates. -/
theorem actual_affine_open_rees_sections_restriction (f : X ⟶ Spec (.of R))
    (I : Ideal R) {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U)) :
    (actualAffineOpenReesSectionsEquiv f I V hV (actualReesOpenSectionsRestriction f I h x)).1 =
      (actualAffineOpenReesSectionsEquiv f I U hU x).1.map (actualOpenSectionsRestriction h) := by
  let := actualAffineOpenCoefficientAlgebra f U
  let := actualAffineOpenCoefficientAlgebra f V
  exact rees_polynomial_restriction_of_generators I
    (actualAffineOpenReesSectionsEquiv f I U hU)
    (actualAffineOpenReesSectionsEquiv f I V hV)
    (actualReesOpenSectionsRestriction f I h) (actualOpenSectionsRestriction h)
    (actual_affine_open_rees_restriction_coefficients f I h hU hV)
    (actual_affine_open_rees_restriction_base_scalars f I h hU hV) x

/-- Each degree coefficient of genuine Rees chart sections commutes with genuine restriction. -/
theorem actual_affine_open_rees_sections_restriction_coeff (f : X ⟶ Spec (.of R))
    (I : Ideal R) {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U)) (n : ℕ) :
    (actualAffineOpenReesSectionsEquiv f I V hV (actualReesOpenSectionsRestriction f I h x)).1.coeff n =
      actualOpenSectionsRestriction h ((actualAffineOpenReesSectionsEquiv f I U hU x).1.coeff n) := by
  rw [actual_affine_open_rees_sections_restriction, Polynomial.coeff_map]

#print axioms actual_affine_open_rees_sections_restriction
#print axioms actual_affine_open_rees_sections_restriction_coeff
end
end Negativity
