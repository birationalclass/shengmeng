module
public import Linear.SmoothLinearTargetParameters
public import Linear.ProjectiveSmoothPointParameters
public import Linear.ProjectiveAmbientFiberCompleteIntersection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Actual centered linear parameters at the original smooth target. -/
def ProjectiveLinearTargetParameterConclusion
    (V : IntegralProjectiveEquations n) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet) (r : ℕ) : Prop :=
    let P := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
    let J := V.affineIdeal.map (algebraMap _ (Localization.AtPrime P))
    ∃ a : Fin r → MvPolynomial (Fin n) ℂ,
      (∀ i, (a i).totalDegree ≤ 1 ∧ MvPolynomial.eval y (a i) = 0) ∧
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime P) (a i)))) =
          (P.map (algebraMap _ (Localization.AtPrime P))).map (Ideal.Quotient.mk J)

theorem IntegralProjectiveEquations.smoothPoint_linear_parameters
    (V : IntegralProjectiveEquations n) (hproper : V.ideal.toIdeal ≠ ⊥)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hs : Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal) :
    ∃ r : ℕ, r = Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) ∧
      ProjectiveLinearTargetParameterConclusion V y hy r := by
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
  obtain ⟨r, a, hr, hlinear, ha⟩ := smoothLocus_constructs_original_linear_parameters
    V.affineIdeal (V.affineIdeal_ne_bot hproper) p y hp
  exact ⟨r, hr, a, hlinear, ha.trans (point_local_quotient_maximalIdeal_map V.affineIdeal P).symm⟩

/-- The SAME actual good target has centered linear parameters with the
SAME r as its original whole fiber cardinality, Krull and differential
dimensions. No independent smooth target or dimension formula is supplied. -/
theorem projective_iterates_whole_ambient_fibers_linear_targets
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
          ProjectiveLinearTargetParameterConclusion V y hy r := by
  obtain ⟨r, hrn, hdim, hrank, hiter⟩ :=
    projective_iterates_whole_ambient_fibers_common_geometry f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, ?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p, hp, hgood, hnonempty, hfiber⟩ := hiter k
  refine ⟨p, hp, hgood, hnonempty, ?_⟩
  intro y hy hyp
  have hgeom := hfiber y hy hyp
  obtain ⟨hS, hSne, hcard, hsource, htarget, hnormal⟩ := hgeom.1
  obtain ⟨s, hs, hlinear⟩ := V.smoothPoint_linear_parameters hproper y hy htarget
  have hsr : s = r := hs.trans hrank
  exact ⟨hgeom, hsr ▸ hlinear⟩

end LinearStudy
