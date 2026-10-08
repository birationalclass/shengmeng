module
public import Linear.ProjectiveLinearSectionDegree
public import Linear.LinearProjectionSectionAvoidance
public import Linear.HomogeneousChartLift
public import Linear.ProjectiveNormalizedConePoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- ONE original linear projection works for every prescribed nonempty affine
principal open. Its actual section contains d=deg V points, ALL in that open.
The target-open polynomial and the actual section may vary with the open;
neither their good behavior nor the degree equality is assumed. -/
theorem projective_exists_linear_sections_in_every_affine_open {n : ℕ}
    (V : IntegralProjectiveEquations n)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree = r ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      (∃ N : ℕ, ∀ j > N, P.eval (j : ℚ) =
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ d : ℕ, 0 < d ∧ (d : ℚ) = (r.factorial : ℚ)*P.leadingCoeff ∧
          ∀ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal →
            ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
              (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
              ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
                w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w) = d ∧
                ∀ z ∈ projectiveLinearSection V L w,
                  z.rep 0 ≠ 0 ∧
                    MvPolynomial.eval (fun i : Fin n => z.rep i.succ/z.rep 0) p ≠ 0 := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,d,c,hd,hdrank,hdHilbert,hc,hex,hsect⟩ :=
    projective_exists_linear_section_hilbert_degree V
  have hdim := projective_chart_krull_dimension_of_hilbertPolynomial V x0 hx0 P hP hHilbert
  rw [hdegree] at hdim
  refine ⟨r,P,hr,hP,hdegree,hdim,hHilbert,L,hL,hinj,hfinite,d,hd,hdHilbert,?_⟩
  intro p hp
  obtain ⟨D,H,hHom,hH,hchart⟩ := projective_exists_homogeneous_chart_avoidance V x0 hx0 p hp
  obtain ⟨b,hb,havoid⟩ := finite_linear_projection_exists_projective_section_avoiding
    V L hL hfinite H hHom hH
  have hcb : c*b ≠ 0 := mul_ne_zero hc hb
  have hnonempty : ∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w (c*b) ≠ 0 := by
    by_contra h
    push Not at h
    apply hcb
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨c*b,hcb,hnonempty,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwc,hwb⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hw0,hcard⟩ := hsect w hwc
  refine ⟨hw0,hcard,?_⟩
  intro z hz
  exact hchart z.rep (havoid w hw0 hwb z hz)

end LinearStudy
