module
public import Linear.ProjectiveLaurentShiftLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {σ : Type} {d l : ℤ}

/-- Original exponent addition is injective on actual allowed weights. -/
theorem homogeneousLaurentAllowedShift_injective {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) :
    Function.Injective (homogeneousLaurentAllowedShift (d := d) a b hb) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  have hh : e.1.1+b.1 = f.1.1+b.1 := congrArg (fun z => z.1.1) h
  exact add_right_cancel hh

/-- The coefficient at a shifted weight is exactly the original
coefficient. This is the actual Finsupp map of the Laurent shift. -/
theorem homogeneousLaurentShiftLinear_coeff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin (n+1) → σ) (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (e : {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a})
    (x : AddMonoidAlgebra R {e : HomogeneousLaurentExponent σ d // e.IsAllowedOn a}) :
    (homogeneousLaurentShiftLinear a b hb x).coeff
      (homogeneousLaurentAllowedShift a b hb e) = x.coeff e := by
  rw [homogeneousLaurentShiftLinear, AddMonoidAlgebra.coeff_mapDomainLinearMap,
    Finsupp.mapDomain_apply_of_injective (homogeneousLaurentAllowedShift_injective a b hb)]
end MvPolynomial
