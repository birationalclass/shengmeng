module
public import Linear.MatrixControlledPolynomialSpan
public import Linear.PolynomialFilteredImage
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy

/-- For an ACTUAL finite polynomial normalization, construct finite module
generators, multiplication matrices and an actual linear bound on the
coefficient degrees of EVERY original polynomial image. -/
theorem finite_normalization_polynomial_filtered_bound
    {k τ σ A : Type*} [Field k] [Finite σ] [CommRing A] [Algebra k A]
    (g : MvPolynomial τ k →ₐ[k] A) (hg : g.Finite)
    (α : MvPolynomial σ k →ₐ[k] A) :
    ∃ (m : ℕ) (b : Fin m → A) (c B : ℕ),
      0 < c ∧ ∀ p : MvPolynomial σ k,
        α p ∈ boundedPolynomialSpan g b (c * p.totalDegree + B) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  let R := MvPolynomial τ k
  letI : Algebra R A := g.toRingHom.toAlgebra
  letI : Module.Finite R A := RingHom.finite_algebraMap.mp hg
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := R) (M := A)
  have hex : ∀ a : A, ∃ u : Fin m → R, ∑ j, g (u j) * b j = a := by
    intro a
    have ha : a ∈ Submodule.span R (Set.range b) := by rw [hb]; trivial
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp ha
    have hu' : ∑ j, (algebraMap R A) (u j) * b j = a := by
      simpa [Algebra.smul_def] using hu
    change ∑ j, g (u j) * b j = a at hu'
    exact ⟨u, hu'⟩
  choose M hM using fun (i : σ) (j : Fin m) => hex (α (MvPolynomial.X i) * b j)
  obtain ⟨u0, hu0⟩ := hex 1
  let c := 1 + Finset.univ.sup (fun z : σ × Fin m × Fin m =>
    (M z.1 z.2.1 z.2.2).totalDegree)
  let B := Finset.univ.sup (fun j : Fin m => (u0 j).totalDegree)
  have hc : 0 < c := by simp [c]
  have hdeg : ∀ i j l, (M i j l).totalDegree ≤ c := by
    intro i j l
    exact (Finset.le_sup (f := fun z : σ × Fin m × Fin m =>
      (M z.1 z.2.1 z.2.2).totalDegree) (Finset.mem_univ (i,j,l))).trans
      (Nat.le_add_left _ _)
  have h1 : (1 : A) ∈ boundedPolynomialSpan g b B := by
    refine ⟨fun j => ⟨u0 j, (MvPolynomial.mem_restrictTotalDegree τ B _).mpr ?_⟩, hu0⟩
    exact Finset.le_sup (f := fun j : Fin m => (u0 j).totalDegree) (Finset.mem_univ j)
  refine ⟨m, b, c, B, hc, ?_⟩
  intro p
  apply polynomial_image_mem_filtration α (boundedPolynomialSpan g b)
    (boundedPolynomialSpan_mono g b) c B h1
  intro N a ha i
  exact boundedPolynomialSpan_mul_of_matrix g b (fun i => α (MvPolynomial.X i))
    M c (fun i j => (hM i j).symm) hdeg N a ha i

end LinearStudy
