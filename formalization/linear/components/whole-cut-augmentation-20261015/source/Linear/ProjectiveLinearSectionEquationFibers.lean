module
public import Linear.ProjectiveLinearSectionDegree
public import Linear.ReducedPolynomialProjectionFibers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original V yields ONE actual linear projection for which the
original equation fibers are radical and have dimension d=degree V,
and the actual projective section has d points on the same derived open.
This compares actual affine equation rings, not a global Proj scheme. -/
theorem projective_exists_linear_section_radical_equation_fibers {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := V.prime
    ∃ (r : ℕ) (P : Polynomial ℚ),r ≤ n ∧ P ≠ 0 ∧ P.natDegree=r ∧
      (∃ N : ℕ,∀ j > N,P.eval (j : ℚ)=
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i,(L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ (d : ℕ) (c : MvPolynomial (Fin (r+1)) ℂ),
          0 < d ∧ (d : ℚ)=(r.factorial : ℚ)*P.leadingCoeff ∧ c ≠ 0 ∧
          (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
          ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
            w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w)=d ∧
            (let J := polynomialProjectionFiberIdeal V.ideal.toIdeal L w;
             J.IsRadical ∧ Module.Finite ℂ (CoordinateRing n ⧸ J) ∧
               Module.finrank ℂ (CoordinateRing n ⧸ J)=d ∧
               Nat.card (MvPolynomial.zeroLocus ℂ J)=d) := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,d,a,hd,hdrank,hdHilbert,ha,_,hsect⟩ :=
    projective_exists_linear_section_hilbert_degree V
  obtain ⟨b,hb,heq⟩ := polynomial_finite_projection_exists_radical_equation_fibers
    V.ideal.toIdeal L hinj hfinite
  have hab : a*b ≠ 0 := mul_ne_zero ha hb
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (a*b) ≠ 0 := by
    by_contra h
    push Not at h
    apply hab
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,d,a*b,hd,hdHilbert,hab,hex,?_⟩
  intro w hw
  have hm : MvPolynomial.eval w a ≠ 0 ∧ MvPolynomial.eval w b ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [map_mul] using hw)
  obtain ⟨hw0,hcard⟩ := hsect w hm.1
  obtain ⟨hrad,hfin,hrank,hpoints⟩ := heq w hm.2
  exact ⟨hw0,hcard,hrad,hfin,hrank.trans hdrank.symm,hpoints.trans hdrank.symm⟩

end LinearStudy
