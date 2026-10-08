module
public import Linear.ProjectiveConeHilbertKrullDimension
public import Linear.NoetherNormalizationTranscendence
public import Linear.FractionFieldTranscendence
public import Linear.ProjectiveConeRatioRatFunc
public import Linear.ProjectiveChartFractionField
public import Mathlib.RingTheory.Spectrum.Prime.Topology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Identify the ACTUAL original affine projective chart's Krull dimension
with the ACTUAL homogeneous Hilbert polynomial degree. The cone and chart
fraction fields and their transcendence comparisons are all constructed. -/
theorem projective_chart_krull_dimension_of_hilbertPolynomial
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hHilbert : ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) =
      (P.natDegree : WithBot ℕ∞) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let F := FractionRing A
  let E := projectiveCoordinateRatioField V
  obtain ⟨a, haDim, haTr⟩ := finiteType_domain_exists_krull_trdeg ℂ A
  have hcone := projective_cone_krull_dimension_of_hilbertPolynomial V P hP hHilbert
  have ha : a = P.natDegree + 1 := by
    have h : (a : WithBot ℕ∞) = ((P.natDegree + 1 : ℕ) : WithBot ℕ∞) :=
      haDim.symm.trans hcone
    exact_mod_cast h
  have hF : Algebra.trdeg ℂ F = ((P.natDegree + 1 : ℕ) : Cardinal) := by
    rw [fraction_field_trdeg ℂ A F, haTr, ha]
  obtain ⟨b, hbDim, hbTr⟩ := finiteType_domain_exists_krull_trdeg ℂ B
  have hE : Algebra.trdeg ℂ E = (b : Cardinal) :=
    (projectiveChartFractionRatioEquiv V x hx).trdeg_eq.symm.trans
      ((fraction_field_trdeg ℂ B (FractionRing B)).trans hbTr)
  have hEF : Algebra.trdeg ℂ F = Algebra.trdeg ℂ E + 1 :=
    (projectiveConeRatioRatFuncEquiv V x hx).restrictScalars ℂ |>.trdeg_eq.symm.trans
      (rational_function_trdeg ℂ E)
  have hb : b = P.natDegree := by
    have h : ((b + 1 : ℕ) : Cardinal.{0}) = ((P.natDegree + 1 : ℕ) : Cardinal.{0}) := by
      simpa [hE, Nat.cast_add, Nat.cast_one] using hEF.symm.trans hF
    have h' : b + 1 = P.natDegree + 1 := by exact_mod_cast h
    omega
  simpa only [hb] using hbDim

/-- The actual affine spectrum underlying the original chart has this
same topological dimension; this is not yet a global Proj comparison. -/
theorem projective_chart_spec_dimension_of_hilbertPolynomial
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hHilbert : ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) :
    topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) =
      (P.natDegree : WithBot ℕ∞) := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact projective_chart_krull_dimension_of_hilbertPolynomial V x hx P hP hHilbert

end LinearStudy
