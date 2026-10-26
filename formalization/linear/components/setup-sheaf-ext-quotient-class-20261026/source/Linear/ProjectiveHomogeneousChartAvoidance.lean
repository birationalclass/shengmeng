module
public import Linear.HomogeneousPullbackComponents
public import Linear.ProjectiveFiberChartAvoidance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The finite original cone map admits a HOMOGENEOUS target polynomial
outside V's ideal whose actual pullback is divisible by the source X0. -/
theorem projectiveConeMap_exists_homogeneous_chart_avoidance_polynomial
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ (k : ℕ) (H C : CoordinateRing n), H.IsHomogeneous k ∧
      H ∉ V.ideal.toIdeal ∧
      (MvPolynomial.aeval f.forms) H - MvPolynomial.X 0 * C ∈ V.ideal.toIdeal := by
  classical
  obtain ⟨H, C, hH, hrel⟩ :=
    projectiveConeMap_exists_chart_avoidance_polynomial f V hq hf hV x hx
  let I := V.ideal.toIdeal
  let J : Ideal (CoordinateRing n) := Ideal.span {MvPolynomial.X 0} ⊔ I
  have hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℂ) := V.ideal.isHomogeneous
  have hX : (Ideal.span ({MvPolynomial.X (0 : Fin (n + 1))} : Set (CoordinateRing n))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule _ ℂ) := by
    apply Ideal.homogeneous_span
    rintro F ⟨rfl⟩
    exact ⟨1, MvPolynomial.isHomogeneous_X ℂ 0⟩
  have hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℂ) := hX.sup hI
  have hfH : MvPolynomial.aeval f.forms H ∈ J := by
    apply Ideal.mem_span_singleton_sup.mpr
    refine ⟨C, MvPolynomial.aeval f.forms H - MvPolynomial.X 0 * C, hrel, ?_⟩
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℕ, MvPolynomial.homogeneousComponent k H ∉ I := by
    by_contra! hall
    exact hH ((MvPolynomial.mem_iff_homogeneousComponent_mem hI H).mpr hall)
  have hcomp : MvPolynomial.aeval f.forms (MvPolynomial.homogeneousComponent k H) ∈ J := by
    rw [← homogeneousComponent_aeval_common_positive_degree f.forms f.degree hq f.homogeneous]
    exact MvPolynomial.homogeneousComponent_mem_of_mem hJ hfH _
  obtain ⟨C', b, hb, he⟩ := Ideal.mem_span_singleton_sup.mp hcomp
  refine ⟨k, MvPolynomial.homogeneousComponent k H, C',
    MvPolynomial.homogeneousComponent_isHomogeneous k H, hk, ?_⟩
  have he' : MvPolynomial.aeval f.forms (MvPolynomial.homogeneousComponent k H) -
      MvPolynomial.X 0 * C' = b := by rw [← he]; ring
  rw [he']
  exact hb

end LinearStudy
