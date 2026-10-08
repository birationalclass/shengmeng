module
public import Linear.BoundedPolynomialCombination
public import Mathlib.Algebra.MvPolynomial.Degrees
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Actual multiplication matrices control the coefficient filtration.
The matrix entries and their finite degree bound will be constructed from
module finiteness; this helper proves their precise filtration consequence. -/
theorem boundedPolynomialSpan_mul_of_matrix
    {k τ σ A : Type*} [Field k] [CommRing A] [Algebra k A] {m : ℕ}
    (g : MvPolynomial τ k →ₐ[k] A) (b : Fin m → A) (x : σ → A)
    (M : σ → Fin m → Fin m → MvPolynomial τ k) (c : ℕ)
    (hM : ∀ i j, x i * b j = ∑ l, g (M i j l) * b l)
    (hdeg : ∀ i j l, (M i j l).totalDegree ≤ c)
    (N : ℕ) (a : A) (ha : a ∈ boundedPolynomialSpan g b N) (i : σ) :
    a * x i ∈ boundedPolynomialSpan g b (N + c) := by
  classical
  obtain ⟨u, rfl⟩ := ha
  let v : Fin m → MvPolynomial τ k := fun l => ∑ j, (u j).val * M i j l
  have hv : ∀ l, (v l).totalDegree ≤ N + c := by
    intro l
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add
      ((MvPolynomial.mem_restrictTotalDegree τ N _).mp (u j).property) (hdeg i j l))
  refine ⟨fun l => ⟨v l, (MvPolynomial.mem_restrictTotalDegree τ _ _).mpr (hv l)⟩, ?_⟩
  change (∑ l, g (v l) * b l) = (∑ j, g (u j) * b j) * x i
  calc
    ∑ l, g (v l) * b l = ∑ l, ∑ j, (g (u j) * g (M i j l)) * b l := by
      simp only [v, map_sum, map_mul, Finset.sum_mul]
    _ = ∑ j, g (u j) * ∑ l, g (M i j l) * b l := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ j, g (u j) * (x i * b j) := by simp_rw [← hM]
    _ = (∑ j, g (u j) * b j) * x i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end LinearStudy
