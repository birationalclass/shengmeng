module
public import Linear.ProjectiveWholeFiberDimensionParameters
public import Linear.ProjectiveGeneralReducedFibers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- For every ORIGINAL iterate, construct ONE nonempty target open on which
EVERY WHOLE fiber has the actual dimension count, is reduced in its actual
equation quotient, and lies in the smooth/unramified locus of the SAME map.
The same dimension also constructs polynomial parameters at every smooth
original chart point. No good-fiber or dimension formula is an input. -/
theorem projective_iterates_whole_good_fibers_same_dimension
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    ∃ r : ℕ, r ≤ n ∧ ringKrullDim B = (r : WithBot ℕ∞) ∧
      Module.finrank B (KaehlerDifferential ℂ B) = r ∧
      (∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
        Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal →
        let Q := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
        let J := V.affineIdeal.map (algebraMap _ (Localization.AtPrime Q))
        ∃ a : Fin r → MvPolynomial (Fin n) ℂ,
          Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
            (algebraMap _ (Localization.AtPrime Q) (a i)))) =
              (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk J)) ∧
      ∀ k : ℕ,
        let F := f.iterate k
        let A := Localization.Away (projectiveChartDenominator F V)
        let φ := projectiveChartOpenMap F V (f.iterate_degree_pos hq k)
          (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
        letI : Algebra B A := φ.toRingHom.toAlgebra
        ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
          (∀ P : PrimeSpectrum A,
            φ (Ideal.Quotient.mk V.affineIdeal p) ∉ P.asIdeal →
            P ∈ Algebra.smoothLocus ℂ A ∧
            PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
            P ∈ Algebra.unramifiedLocus B A) ∧
          (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
          ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
            MvPolynomial.eval y p ≠ 0 →
            (F.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
            (∀ (v : CoordinateVector n) (hv : v ≠ 0),
              F.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
            Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal F V y) ∧
            IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal F V y) ∧
            Nat.card (F.onPoints ⁻¹' {normalizedProjectivePoint y}) = (f.degree ^ k) ^ r := by
  intro B
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  obtain ⟨r, hrn, hdim, hrank, hparams, hiter⟩ :=
    projective_whole_fibers_and_smooth_parameters_same_dimension f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, hparams, ?_⟩
  intro k F A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p₀, hp₀, hgood, _, hred⟩ := projective_exists_general_whole_reduced_fibers
    F V (f.iterate_degree_pos hq k) (f.iterate_surjective hf k)
    (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
  obtain ⟨p₁, hp₁, _, hcount⟩ := hiter k
  let p := p₀ * p₁
  have hp : p ∉ V.affineIdeal := by
    intro h
    rcases (show V.affineIdeal.IsPrime from inferInstance).mem_or_mem h with h₀ | h₁
    · exact hp₀ h₀
    · exact hp₁ h₁
  obtain ⟨y₀, hy₀, hyp, _⟩ := V.exists_smooth_affine_point_avoiding x0 hx0 p hp
  refine ⟨p, hp, ?_, ⟨y₀, hy₀, hyp⟩, ?_⟩
  · intro P hP
    apply hgood P
    intro h₀
    apply hP
    change φ (Ideal.Quotient.mk V.affineIdeal (p₀ * p₁)) ∈ P.asIdeal
    rw [map_mul, map_mul]
    exact P.asIdeal.mul_mem_right _ h₀
  · intro y hy hyp
    have heval : MvPolynomial.eval y p₀ ≠ 0 ∧ MvPolynomial.eval y p₁ ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [p, MvPolynomial.eval_mul] using hyp)
    obtain ⟨hfinite, hchart, hfin, hreduce, _⟩ := hred y hy heval.1
    exact ⟨hfinite, hchart, hfin, hreduce, (hcount y hy heval.2).2⟩

end LinearStudy
