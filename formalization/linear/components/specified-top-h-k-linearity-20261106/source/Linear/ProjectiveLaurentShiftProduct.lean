module
public import Linear.ProjectiveLaurentReindexShift
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {R : Type*} [CommRing R] {σ : Type} {d l : ℤ}

/-- Linearly shifting global homogeneous coordinates is actual local
Laurent monomial multiplication, followed by the new-degree reindexing. -/
theorem homogeneousLaurentShiftLinear_product {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (x : AddMonoidAlgebra R (laurentExponentSubmonoid (coordinateTailExponent a))) :
    homogeneousLaurentShiftLinear (d := d) a b hb
      (AddMonoidAlgebra.mapDomainLinearEquiv R R (coordinateLaurentExponentEquiv a d) x) =
    AddMonoidAlgebra.mapDomainLinearEquiv R R (coordinateLaurentExponentEquiv a (d+l))
      (AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent a b hb) 1 * x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  | single e r =>
    simp only [AddMonoidAlgebra.mapDomainLinearEquiv_single,
      homogeneousLaurentShiftLinear, AddMonoidAlgebra.mapDomainLinearMap_single,
      AddMonoidAlgebra.single_mul_single, one_mul]
    rw [add_comm (homogeneousLaurentShiftLocalExponent a b hb) e,
      coordinateLaurentExponentEquiv_shift]
end MvPolynomial
