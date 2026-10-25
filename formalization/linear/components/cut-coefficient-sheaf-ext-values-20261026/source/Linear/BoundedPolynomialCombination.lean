module
public import Linear.PolynomialRectangleDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {k τ A : Type*} [Field k] [CommRing A] [Algebra k A] {m : ℕ}

/-- ACTUAL bounded coefficient combinations for a polynomial normalization. -/
def boundedPolynomialCombination (g : MvPolynomial τ k →ₐ[k] A)
    (b : Fin m → A) (N : ℕ) :
    (Fin m → MvPolynomial.restrictTotalDegree τ k N) →ₗ[k] A where
  toFun c := ∑ j, g (c j) * b j
  map_add' c d := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [map_smul, smul_mul_assoc, Finset.smul_sum]

def boundedPolynomialSpan (g : MvPolynomial τ k →ₐ[k] A)
    (b : Fin m → A) (N : ℕ) : Submodule k A :=
  (boundedPolynomialCombination g b N).range

theorem boundedPolynomialSpan_mono (g : MvPolynomial τ k →ₐ[k] A) (b : Fin m → A) :
    Monotone (boundedPolynomialSpan g b) := by
  intro N M hNM a ha
  obtain ⟨c, rfl⟩ := ha
  refine ⟨fun j => ⟨c j, (MvPolynomial.mem_restrictTotalDegree τ M _).mpr
    (((MvPolynomial.mem_restrictTotalDegree τ N _).mp (c j).property).trans hNM)⟩, rfl⟩

theorem boundedPolynomialSpan_finite [Finite τ]
    (g : MvPolynomial τ k →ₐ[k] A) (b : Fin m → A) (N : ℕ) :
    Module.Finite k (boundedPolynomialSpan g b N) := by
  unfold boundedPolynomialSpan
  infer_instance

/-- A rank bound from the ACTUAL source space, without a hypothetical
Hilbert polynomial or coefficient-boundedness assumption. -/
theorem boundedPolynomialSpan_finrank_le [Finite τ]
    (g : MvPolynomial τ k →ₐ[k] A) (b : Fin m → A) (N : ℕ) :
    Module.finrank k (boundedPolynomialSpan g b N) ≤ m * (N + 1) ^ Nat.card τ := by
  have h1 := LinearMap.finrank_range_le (boundedPolynomialCombination g b N)
  have h2 := Submodule.finrank_mono (MvPolynomial.restrictTotalDegree_le_restrictDegree τ k N)
  have h3 := Nat.mul_le_mul_left m h2
  have h1' : Module.finrank k (boundedPolynomialSpan g b N) ≤
      m * Module.finrank k (MvPolynomial.restrictTotalDegree τ k N) := by
    simpa [boundedPolynomialSpan, Module.finrank_pi_fintype] using h1
  rw [polynomial_restrictDegree_finrank k τ N] at h3
  exact h1'.trans h3

end LinearStudy
