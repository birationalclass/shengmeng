module
public import Linear.ProjectiveChartHilbertDegree
public import Linear.ProjectiveIteratedWholeFiberDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- One actual Hilbert polynomial of original V controls EVERY original
iterate's WHOLE general point fibers. Geometry/dimension is not an input
and geometric dimension comparison remains a separate obligation. -/
theorem projective_iterates_whole_fiber_hilbert_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      (∃ K : ℕ, ∀ N > K,
        P.eval (N : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal N : ℚ)) ∧
      ∀ k : ℕ, ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
            Nat.card ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}) =
              (f.degree ^ k) ^ P.natDegree := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  obtain ⟨P, hP, hdeg, hD, hHilbert⟩ :=
    projectiveChartField_exists_hilbert_degree_power f V hq hf hV x0 hx0
  obtain ⟨_, hiter⟩ := projective_iterates_general_whole_fiber_degree f V hq hf hV x0 hx0
  refine ⟨P, hP, hdeg, hHilbert, ?_⟩
  intro k
  obtain ⟨p, hp, hnonempty, hcard⟩ := hiter k
  refine ⟨p, hp, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨hfinite, hpoints⟩ := hcard y hy hyp
  refine ⟨hfinite, ?_⟩
  calc
    Nat.card ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}) =
        (f.degree ^ P.natDegree) ^ k := hpoints.trans (congrArg (fun z : ℕ => z ^ k) hD)
    _ = (f.degree ^ k) ^ P.natDegree := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end LinearStudy
