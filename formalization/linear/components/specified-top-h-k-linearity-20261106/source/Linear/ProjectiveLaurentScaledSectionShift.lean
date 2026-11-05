module
public import Linear.ProjectiveLaurentSectionShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {B : Type*} [CommRing B] {σ : Type} {d l : ℤ}

/-- Actual Laurent multiplication by a monomial with arbitrary coefficient. -/
theorem homogeneousLaurentShiftLinear_scaled_product {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) (q : B)
    (x : AddMonoidAlgebra B (laurentExponentSubmonoid (coordinateTailExponent a))) :
    AddMonoidAlgebra.mapDomainLinearEquiv B B (coordinateLaurentExponentEquiv a (d+l))
      (AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent a b hb) q * x) =
    q • homogeneousLaurentShiftLinear (d := d) a b hb
      (AddMonoidAlgebra.mapDomainLinearEquiv B B (coordinateLaurentExponentEquiv a d) x) := by
  have h : AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent a b hb) q =
      q • AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent a b hb) (1:B) := by
    rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [h, smul_mul_assoc, map_smul, ← homogeneousLaurentShiftLinear_product]

variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The previous section comparison now preserves arbitrary actual base
coefficients, needed for general homogeneous polynomial multiplication. -/
theorem coordinateHomogeneousLaurent_section_scaled_multiply {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (q : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
    (c r : Γ(Proj (homogeneousSubmodule σ R), coordinateOpenCechIntersection (R := R) a))
    (hc : coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a c =
      AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent (fun j => (a j).down) b hb) q) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a (d+l) (c*r) =
    q • homogeneousLaurentShiftLinear _ b hb
      (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d r) := by
  unfold coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
  simp only [LinearEquiv.trans_apply]
  change AddMonoidAlgebra.mapDomainLinearEquiv _ _ _
      (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a (c*r)) =
    q • homogeneousLaurentShiftLinear _ b hb
      (AddMonoidAlgebra.mapDomainLinearEquiv _ _ _
        (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a r))
  rw [map_mul, hc]
  exact homogeneousLaurentShiftLinear_scaled_product _ b hb q _

end MvPolynomial
