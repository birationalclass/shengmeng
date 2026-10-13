module
public import Linear.ProjectiveNegativeWeightComplement
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {σ : Type} [Fintype σ]

/-- The exponent identity controlling the transpose of actual monomial
multiplication: multiplying a negative monomial by b extracts a=b+c.
This is an exponent lemma, not yet the sheaf multiplication comparison. -/
theorem projective_complement_multiplication_iff (m l : ℕ)
    (a : ProjectiveMonomialIndex σ (m+l)) (b : ProjectiveMonomialIndex σ l)
    (c : ProjectiveMonomialIndex σ m) :
    (∀ i, (projectiveMonomialNegativeWeight (m+l) a).1.1 i + (b.1 i : ℤ) =
      (projectiveMonomialNegativeWeight m c).1.1 i) ↔ a.1 = b.1+c.1 := by
  simp only [projectiveMonomialNegativeWeight_apply]
  constructor
  · intro h
    ext i
    have hi := h i
    simp only [Finsupp.add_apply]
    omega
  · intro h i
    have hi := congrArg (fun f : σ →₀ ℕ => f i) h
    simp only [Finsupp.add_apply] at hi
    omega

/-- A product contributes to the canonical residue exactly at the
complementary monomial. -/
theorem projective_negative_weight_residue_iff (m : ℕ)
    (e : ProjectiveNegativeWeight σ m) (a : ProjectiveMonomialIndex σ m) :
    (∀ i, e.1.1 i + (a.1 i : ℤ) = -1) ↔ e = projectiveMonomialNegativeWeight m a := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    ext i
    rw [projectiveMonomialNegativeWeight_apply]
    have := h i
    omega
  · rintro rfl i
    rw [projectiveMonomialNegativeWeight_apply]
    omega
end MvPolynomial
