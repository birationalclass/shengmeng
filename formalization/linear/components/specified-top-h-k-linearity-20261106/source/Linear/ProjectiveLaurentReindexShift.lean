module
public import Linear.ProjectiveLaurentShiftLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {σ : Type} {d l : ℤ}

/-- The reconstructed anchor coordinate makes local exponent addition
agree with global homogeneous exponent addition. -/
theorem coordinateLaurentExponentEquiv_add {n : ℕ} (a : Fin (n+1) → σ)
    (e f : laurentExponentSubmonoid (coordinateTailExponent a)) :
    (coordinateLaurentExponentEquiv a (d+l) (e+f)).1.1 =
      (coordinateLaurentExponentEquiv a d e).1.1 +
        (coordinateLaurentExponentEquiv a l f).1.1 := by
  ext i
  by_cases hi : i = a 0
  · subst i
    simp only [Finsupp.add_apply, coordinateLaurentExponentEquiv_apply_anchor]
    change d+l-(e.1+f.1).degree = (d-e.1.degree)+(l-f.1.degree)
    rw [map_add]
    omega
  · simp only [Finsupp.add_apply, coordinateLaurentExponentEquiv_apply_of_ne a _ _ i hi]
    rfl

/-- The actual local Laurent exponent of a globally nonnegative monomial. -/
def homogeneousLaurentShiftLocalExponent {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i) :
    laurentExponentSubmonoid (coordinateTailExponent a) :=
  (coordinateLaurentExponentEquiv a l).symm ⟨b, by
    intro i hi
    exact (not_lt_of_ge (hb i) hi).elim⟩

theorem coordinateLaurentExponentEquiv_shift {n : ℕ} (a : Fin (n+1) → σ)
    (b : HomogeneousLaurentExponent σ l) (hb : ∀ i, 0 ≤ b.1 i)
    (e : laurentExponentSubmonoid (coordinateTailExponent a)) :
    coordinateLaurentExponentEquiv a (d+l) (e+homogeneousLaurentShiftLocalExponent a b hb) =
      homogeneousLaurentAllowedShift a b hb (coordinateLaurentExponentEquiv a d e) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coordinateLaurentExponentEquiv_add]
  have h := congrArg (fun z => z.1.1)
    ((coordinateLaurentExponentEquiv a l).apply_symm_apply
      (⟨b, by intro i hi; exact (not_lt_of_ge (hb i) hi).elim⟩ :
        {e : HomogeneousLaurentExponent σ l // e.IsAllowedOn a}))
  change _ + _ = _ + _
  exact congrArg ((coordinateLaurentExponentEquiv a d e).1.1 + ·) h
end MvPolynomial
