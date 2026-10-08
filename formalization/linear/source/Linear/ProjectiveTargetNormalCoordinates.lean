module
public import Linear.OriginalPolynomialNormal
public import Linear.ProjectiveDifferentialDimension
public import Linear.ProjectiveSmoothLinearParameters
public import Linear.FirstJetNormalForm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual original target ideal in constructed affine linear coordinates,
with its normal polynomial first jet. This is output, not supplied data. -/
def ProjectiveTargetNormalCoordinateConclusion {n : ℕ}
    (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) (r : ℕ) : Prop :=
    ∃ (c : ℕ), c = n-r ∧ 0 < c ∧
      ∃ (e : (Fin r ⊕ Fin c) ≃ Fin n)
        (M : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) ℂ) (hM : Matrix.det M ≠ 0)
        (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ),
        let z := M⁻¹ *ᵥ (y ∘ e)
        let C := (polynomialLinearChangeEquiv M hM).toRingHom.comp
          (MvPolynomial.rename e.symm).toRingHom
        let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) z).toRingHom
        letI : Q.IsPrime := RingHom.ker_isPrime _
        (∀ i, MvPolynomial.eval z (H i) = 0) ∧
        (∀ i j, MvPolynomial.eval z (MvPolynomial.pderiv j (H i)) =
          if j = Sum.inr i then 1 else 0) ∧
        (V.affineIdeal.map C).map (algebraMap _ (Localization.AtPrime Q)) =
          Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))) ∧
        (∀ i, formalPolynomialAtPoint z (H i) - MvPowerSeries.X (Sum.inr i) ∈
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) ℂ)) ^ 2) ∧
        V.affineIdeal.map ((formalPolynomialAtPoint z).comp C) =
          Ideal.span (Set.range (fun i => formalPolynomialAtPoint z (H i)))

/-- At the actual original smooth target, construct the polynomial normal
presentation required by the common-Jacobian argument. r and c are derived
from the original chart, not supplied as independent dimensions. -/
theorem IntegralProjectiveEquations.smoothTarget_actual_normal_coordinates {n : ℕ}
    (V : IntegralProjectiveEquations n) (hproper : V.ideal.toIdeal ≠ ⊥)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hs : Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal) :
    ∃ r : ℕ,
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      ProjectiveTargetNormalCoordinateConclusion V y r := by
  classical
  letI : V.affineIdeal.IsPrime := V.affineIdeal_isPrime_of_point y hy
  let p := (V.affinePoint y hy).asIdeal
  letI : p.IsPrime := inferInstance
  letI : Algebra.IsSmoothAt ℂ p := hs
  let P := p.comap (Ideal.Quotient.mk V.affineIdeal)
  letI : P.IsPrime := inferInstance
  have hp : P = RingHom.ker (MvPolynomial.aeval (R := ℂ) y).toRingHom :=
    V.affinePointIdeal_comap y hy
  have hIP : V.affineIdeal ≤ P := by
    intro F hF
    change Ideal.Quotient.mk V.affineIdeal F ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
    exact p.zero_mem
  let J := V.affineIdeal.map (algebraMap _ (Localization.AtPrime P))
  letI : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top V.affineIdeal P hIP)
  letI : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : Algebra.FormallySmooth ℂ (Localization.AtPrime P ⧸ J) :=
    quotient_smoothAt_formallySmooth_localized_ideal V.affineIdeal p
  have hloc : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot (V.affineIdeal_ne_bot hproper)
  obtain ⟨r, c, hc, e, M, hM, H, hr, h0, hD, hlocal⟩ :=
    smooth_point_original_ideal_normal_polynomial_generators V.affineIdeal P hIP y hp hloc
  have hrank : Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
      (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r :=
    (hr.trans (polynomial_local_differential_finrank V.affineIdeal P hIP)).symm
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) := by
    rw [V.chart_krull_dimension_eq_differential_rank y hy, hrank]
  have hcard : r+c = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  have hcr : c = n-r := by omega
  letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  let z := M⁻¹ *ᵥ (y ∘ e)
  let C := (polynomialLinearChangeEquiv M hM).toRingHom.comp
    (MvPolynomial.rename e.symm).toRingHom
  let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) z).toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime _
  have hfirst := normal_firstOrder_of_derivative_coordinates
    (fun i => formalPolynomialAtPoint z (H i))
    (fun i => (formalPolynomialAtPoint_constantCoeff z (H i)).trans (h0 i))
    (fun i j => (by
      rw [formalPolynomialAtPoint_pderiv, formalPolynomialAtPoint_constantCoeff]
      exact hD i j))
  have hformal := formalPolynomialIdeal_local_generators (V.affineIdeal.map C) Q z rfl H hlocal
  rw [Ideal.map_map] at hformal
  exact ⟨r, hdim, hrank, c, hcr, hc, e, M, hM, H, h0, hD, hlocal, hfirst, hformal⟩

/-- Target normal equations are constructed at the SAME original target as
the whole ambient fiber and its linear parameters, for every original iterate.
All three constructions use the SAME actual r. -/
theorem projective_iterates_whole_ambient_fibers_normal_targets {n : ℕ}
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
          ProjectiveWholeAmbientFiberConclusion (f.iterate k) V y hy r ∧
          ProjectiveLinearTargetParameterConclusion V y hy r ∧
          ProjectiveTargetNormalCoordinateConclusion V y r := by
  obtain ⟨r, hrn, hdim, hrank, hiter⟩ :=
    projective_iterates_whole_ambient_fibers_linear_targets f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, ?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p, hp, hgood, hnonempty, hfiber⟩ := hiter k
  refine ⟨p, hp, hgood, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨hgeom, hlinear⟩ := hfiber y hy hyp
  obtain ⟨hS, hSne, hcard, hsource, htarget, hnormal⟩ := hgeom.1
  obtain ⟨s, hsdim, hsrank, htargetnormal⟩ :=
    V.smoothTarget_actual_normal_coordinates hproper y hy htarget
  have hsr : s = r := hsrank.symm.trans hrank
  exact ⟨hgeom, hlinear, hsr ▸ htargetnormal⟩

end LinearStudy
