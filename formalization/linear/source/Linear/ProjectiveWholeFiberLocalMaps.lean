module
public import Linear.ProjectiveCenteredNormalTarget
public import Linear.ProjectiveWholeFiberPointLoci
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Explicit output: all source points of the original whole fiber have the
actual ambient local quotient pullback, with the SAME actual target prime. -/
def ProjectiveWholeFiberLocalMapConclusion {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (y : Fin n → ℂ) : Prop :=
    ∀ z : Fin n → ℂ, z ∈ MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) →
      ∃ hp0 : MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) ≠ 0,
      let p0 := affineChartPolynomialMap (f.forms 0)
      let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
      let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
      let P := RingHom.ker (polynomialAwayPointEvaluation z p0 hp0).toRingHom
      letI : P.IsPrime := RingHom.ker_isPrime _
      let Q := P.comap (rationalPolynomialChartMap p0 p).toRingHom
      let hI := projectiveRationalPolynomialChartMap_ideal f V hq hf hV x0 hx0
      Q = RingHom.ker (MvPolynomial.aeval (R := ℂ) y).toRingHom ∧
      (generalPointLocalQuotientPullback V.affineIdeal J P Q
        (rationalPolynomialChartMap p0 p).toRingHom rfl hI).FormallyUnramified

theorem projective_whole_fiber_actual_local_maps {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (b : MvPolynomial (Fin n) ℂ)
    (hgood : let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
      let A := Localization.Away (projectiveChartDenominator f V)
      let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
      letI : Algebra B A := φ.toRingHom.toAlgebra
      ∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal b) ∉ P.asIdeal →
        P ∈ Algebra.smoothLocus ℂ A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
        P ∈ Algebra.unramifiedLocus B A)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hb : MvPolynomial.eval y b ≠ 0) :
    ProjectiveWholeFiberLocalMapConclusion f V hq hf hV x0 hx0 y := by
  intro z hzF
  have hz := (projectiveAffineFiberIdeal_point f V y z hzF).1
  have hfy := (projectiveAffineFiberIdeal_point f V y z hzF).2.2
  obtain ⟨hp0, _, _, hu, _⟩ := projective_whole_fiber_point_actual_good_loci
    f V hq hf hV x0 hx0 b hgood y z hy hz hb hfy
  refine ⟨hp0, ?_, ?_⟩
  · have hrat : (fun i : Fin n => MvPolynomial.eval z (affineChartPolynomialMap (f.forms i.succ)) /
        MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0))) = y := by
      funext i
      apply (div_eq_iff hp0).mpr
      have h := hzF _ ((show Ideal.span (Set.range (fun j : Fin n =>
          affineChartPolynomialMap (f.forms j.succ) -
            MvPolynomial.C (y j) * affineChartPolynomialMap (f.forms 0))) ≤
            projectiveAffineFiberIdeal f V y from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self i)))
      change MvPolynomial.eval z _ = 0 at h
      simpa only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        sub_eq_zero] using h
    have hker := rationalPolynomialChartMap_point_kernel z
      (affineChartPolynomialMap (f.forms 0)) hp0
      (fun i : Fin n => affineChartPolynomialMap (f.forms i.succ))
    rw [hrat] at hker
    exact hker.symm
  · exact projectiveAmbientChart_unramified_at_affine_coordinates f V hq hf hV x0 hx0
      (projectiveChartPointEvaluation f V z hz hp0) hu z
      (projectiveChartPointEvaluation_source_coordinates f V z hz hp0) hp0

/-- No local unramification data are supplied: for EVERY original iterate,
derive them at ALL original source points over the same constructed good
target open, alongside the same ambient fiber and centered normal target. -/
theorem projective_iterates_whole_fibers_actual_local_maps {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      ∀ k : ℕ,
        let F := f.iterate k
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let A := Localization.Away (projectiveChartDenominator F V)
        let φ := projectiveChartOpenMap F V (f.iterate_degree_pos hq k)
          (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
        letI : Algebra B A := φ.toRingHom.toAlgebra
        ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal p) ∉ P.asIdeal →
          P ∈ Algebra.smoothLocus ℂ A ∧
          PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
          P ∈ Algebra.unramifiedLocus B A) ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          ProjectiveWholeAmbientFiberConclusion F V y hy r ∧
          ProjectiveCenteredNormalTargetConclusion V y r ∧
          ProjectiveWholeFiberLocalMapConclusion F V (f.iterate_degree_pos hq k)
            (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0 y := by
  obtain ⟨r, hrn, hdim, hrank, hiter⟩ :=
    projective_iterates_whole_fibers_centered_normal_targets f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, ?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p, hp, hgood, hnonempty, htarget⟩ := hiter k
  refine ⟨p, hp, hgood, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨hgeom, _, hnormal⟩ := htarget y hy hyp
  exact ⟨hgeom, hnormal, projective_whole_fiber_actual_local_maps F V
    (f.iterate_degree_pos hq k) (f.iterate_surjective hf k)
    (f.iterate_total_invariance V.zeroSet hV k) x0 hx0 p hgood y hy hyp⟩

end LinearStudy
