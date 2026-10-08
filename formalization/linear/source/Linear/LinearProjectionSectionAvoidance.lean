module
public import Linear.ProjectiveLinearSectionPointEquiv
public import Linear.FiniteLinearProjectionGoodOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The whole actual coordinate fiber avoids a specified proper source hypersurface. -/
theorem finite_polynomial_projection_exists_cone_fiber_avoiding
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (L : τ → MvPolynomial σ K)
    (hfinite : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)).Finite)
    (H : MvPolynomial σ K) (hH : H ∉ I) :
    ∃ b : MvPolynomial τ K, b ≠ 0 ∧
      ∀ (w : τ → K), MvPolynomial.eval w b ≠ 0 →
        ∀ (v : σ → K), v ∈ MvPolynomial.zeroLocus K I →
          (fun i => MvPolynomial.eval v (L i)) = w → MvPolynomial.eval v H ≠ 0 := by
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Module.Finite R A := hfinite
  have hHa : Ideal.Quotient.mk I H ≠ 0 := by
    intro hz
    exact hH (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  obtain ⟨b,hb,havoid⟩ := ringHom_algebraic_target_open_avoids_source_closed
    φ.toRingHom inferInstance (Ideal.Quotient.mk I H) hHa
  refine ⟨b,hb,?_⟩
  intro w hw v hv hvL
  let point := polynomialProjectionFiberPointEquiv I L w ⟨⟨v,hv⟩,hvL⟩
  have hpoint : point.val.comp φ = MvPolynomial.aeval w := point.property
  have hbval : point.val (φ b) = MvPolynomial.eval w b := by
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_eq_eval] using AlgHom.congr_fun hpoint b
  have hnot : φ b ∉ (rationalPointPrime point.val).asIdeal := by
    change point.val (φ b) ≠ 0
    rwa [hbval]
  have hsource := havoid (rationalPointPrime point.val) hnot
  change point.val (Ideal.Quotient.mk I H) ≠ 0 at hsource
  simpa [point,polynomialProjectionFiberPointEquiv,polynomialZeroLocusPointEquiv,
    MvPolynomial.aeval_eq_eval] using hsource

/-- Whole ACTUAL projective linear sections avoid a specified homogeneous
proper hypersurface. Homogeneous scaling carries cone avoidance to projective
representatives; no pointwise avoidance is supplied as input. -/
theorem finite_linear_projection_exists_projective_section_avoiding {n r D : ℕ}
    (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (H : CoordinateRing n) (hHom : H.IsHomogeneous D) (hH : H ∉ V.ideal.toIdeal) :
    ∃ b : MvPolynomial (Fin (r+1)) ℂ, b ≠ 0 ∧
      ∀ (w : Fin (r+1) → ℂ), w 0 ≠ 0 → MvPolynomial.eval w b ≠ 0 →
        ∀ p ∈ projectiveLinearSection V L w, MvPolynomial.eval p.rep H ≠ 0 := by
  letI := V.prime
  obtain ⟨b,hb,havoid⟩ := finite_polynomial_projection_exists_cone_fiber_avoiding
    V.ideal.toIdeal L hfinite H hH
  have hfree : ∀ (v : CoordinateVector n), v ≠ 0 →
      (∀ P ∈ V.ideal.toIdeal, MvPolynomial.eval v P=0) →
      (fun i => MvPolynomial.eval v (L i)) ≠ 0 := by
    intro v hv hV hz
    apply hv
    apply integral_linear_normalization_origin_zeroLocus V.ideal.toIdeal
      V.ideal.isHomogeneous L hL (projectiveLinearNormalizationMap V L)
      (fun i => by simp [projectiveLinearNormalizationMap]) hfinite.to_isIntegral v hV
    intro i
    exact congrFun hz i
  refine ⟨b,hb,?_⟩
  intro w hw0 hw p hp
  let v := p.rep
  have hv : v ≠ 0 := Projectivization.rep_nonzero p
  have hvI : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := hp.1
  have hrel (i) : MvPolynomial.eval v (L i)*w 0=w i*MvPolynomial.eval v (L 0) := hp.2 i
  have hL0 : MvPolynomial.eval v (L 0) ≠ 0 := by
    intro hz
    apply hfree v hv hvI
    funext i
    have hi := hrel i
    rw [hz,mul_zero] at hi
    exact (mul_eq_zero.mp hi).resolve_right hw0
  let a : ℂ := w 0 / MvPolynomial.eval v (L 0)
  have hscaledV := homogeneous_zeroLocus_smul V.ideal.toIdeal V.ideal.isHomogeneous v hvI a
  have hscaledL : (fun i => MvPolynomial.eval (a • v) (L i))=w := by
    funext i
    rw [homogeneous_eval_smul (hL i),pow_one]
    dsimp [a]
    field_simp [hL0]
    simpa only [mul_comm] using hrel i
  have hn := havoid w hw (a • v) hscaledV hscaledL
  rw [homogeneous_eval_smul hHom] at hn
  exact (mul_ne_zero_iff.mp hn).2

end LinearStudy
