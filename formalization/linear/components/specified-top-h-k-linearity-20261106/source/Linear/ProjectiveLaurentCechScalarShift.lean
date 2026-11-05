module
public import Linear.ProjectiveLaurentCechShiftCoefficients
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ] {d l : ℤ}

/-- Scaling the actual product cochain map scales every actual tuple map. -/
theorem coordinateLaurentCechShift_scalar_lift (b : HomogeneousLaurentExponent σ l)
    (hb : ∀ i, 0 ≤ b.1 i)
    (q : Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) (n : ℕ) :
    q • coordinateLaurentCechShift (R := R) (d := d) b hb n =
    Pi.lift (fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      coordinateLaurentTupleProjection (R := R) d a ≫
        (q • ModuleCat.ofHom (homogeneousLaurentShiftLinear (fun j => (a.1 j).down) b hb))) := by
  unfold coordinateLaurentCechShift coordinateLaurentTupleProjection
  apply Pi.hom_ext
  intro a
  rw [Linear.smul_comp, Pi.lift_comp_π, Pi.lift_comp_π, Linear.comp_smul]

end MvPolynomial
