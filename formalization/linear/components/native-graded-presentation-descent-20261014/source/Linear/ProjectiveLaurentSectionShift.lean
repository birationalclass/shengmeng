module
public import Linear.ProjectiveLaurentShiftProduct
public import Linear.ProjectiveCechLaurentSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {σ : Type} {d l : ℤ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous reindexing of actual section multiplication is the proved
global Laurent shift whenever the multiplying section is the chart monomial. -/
theorem coordinateHomogeneousLaurent_section_multiply {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (c r : Γ(Proj (homogeneousSubmodule σ R), coordinateOpenCechIntersection (R := R) a))
    (hc : coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a c =
      AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent (fun j => (a j).down) b hb) 1) :
    coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a (d+l) (c*r) =
      homogeneousLaurentShiftLinear _ b hb
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d r) := by
  unfold coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
  simp only [LinearEquiv.trans_apply]
  change AddMonoidAlgebra.mapDomainLinearEquiv _ _ _
    (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a (c*r)) =
    homogeneousLaurentShiftLinear _ b hb
      (AddMonoidAlgebra.mapDomainLinearEquiv _ _ _
        (coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a r))
  rw [map_mul, hc]
  exact (homogeneousLaurentShiftLinear_product _ b hb _).symm
end MvPolynomial
