module
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Degree-controlled evaluation into an ACTUAL increasing linear filtration.
It is enough to control multiplication by the actual images of the variables;
no coefficient representations or degree conclusion are supplied. -/
theorem polynomial_image_mem_filtration
    {k σ A : Type*} [Field k] [CommRing A] [Algebra k A]
    (α : MvPolynomial σ k →ₐ[k] A) (G : ℕ → Submodule k A)
    (hmono : Monotone G) (c B : ℕ) (h1 : (1 : A) ∈ G B)
    (hX : ∀ (N : ℕ) (a : A), a ∈ G N → ∀ i : σ,
      a * α (MvPolynomial.X i) ∈ G (N + c))
    (p : MvPolynomial σ k) :
    α p ∈ G (c * p.totalDegree + B) := by
  classical
  induction p using MvPolynomial.induction_on'' with
  | C a =>
      simpa [Algebra.smul_def] using (G B).smul_mem a h1
  | monomial_add e a p he ha hp hm =>
      have hms : (MvPolynomial.monomial e a : MvPolynomial σ k).support ⊆
          (MvPolynomial.monomial e a + p).support := by
        intro v hv
        have hv' : v = e := by simpa [MvPolynomial.support_monomial, ha] using hv
        subst v
        have hpe : p.coeff e = 0 := by simpa [MvPolynomial.mem_support_iff] using he
        simp [MvPolynomial.mem_support_iff, hpe, ha]
      have hps : p.support ⊆ (MvPolynomial.monomial e a + p).support := by
        intro v hv
        have hve : v ≠ e := by intro h; subst v; exact he hv
        simpa [MvPolynomial.mem_support_iff,
          MvPolynomial.coeff_monomial, hve, Ne.symm hve] using hv
      rw [map_add]
      apply (G _).add_mem
      · exact hmono (Nat.add_le_add_right (Nat.mul_le_mul_left c
          (MvPolynomial.totalDegree_le_of_support_subset hms)) B) hm
      · exact hmono (Nat.add_le_add_right (Nat.mul_le_mul_left c
          (MvPolynomial.totalDegree_le_of_support_subset hps)) B) hp
  | mul_X p i hp =>
      by_cases hz : p = 0
      · simp [hz]
      · have hdeg : (p * MvPolynomial.X i).totalDegree = p.totalDegree + 1 := by
          rw [MvPolynomial.totalDegree_mul_of_isDomain hz (MvPolynomial.X_ne_zero i),
            MvPolynomial.totalDegree_X]
        rw [map_mul, hdeg]
        convert hX (c * p.totalDegree + B) (α p) hp i using 1 <;> congr 1 <;> ring

end LinearStudy
