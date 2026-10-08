module
public import Linear.CenteredTargetNormalCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Output on the SAME original target, now in its centered coordinates.
The ideal and linear changes are actual images of the original V. -/
def ProjectiveCenteredNormalTargetConclusion {n : ℕ}
    (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) (r : ℕ) : Prop :=
    ∃ c : ℕ, c = n-r ∧ 0 < c ∧
      ∃ (e : (Fin r ⊕ Fin c) ≃ Fin n)
        (M : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) ℂ) (hM : Matrix.det M ≠ 0)
        (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ),
        let z := M⁻¹ *ᵥ (y ∘ e)
        let C := (polynomialTranslation z).toRingHom.comp
          ((polynomialLinearChangeEquiv M hM).toRingHom.comp
            (MvPolynomial.rename e.symm).toRingHom)
        let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin r ⊕ Fin c → ℂ)).toRingHom
        letI : Q.IsPrime := RingHom.ker_isPrime _
        V.affineIdeal.map C ≤ Q ∧
        (∀ i, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ) (H i) = 0) ∧
        (∀ i j, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ)
          (MvPolynomial.pderiv j (H i)) = if j = Sum.inr i then 1 else 0) ∧
        (V.affineIdeal.map C).map (algebraMap _ (Localization.AtPrime Q)) =
          Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))

theorem projective_actual_normal_target_centering {n : ℕ}
    (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) (r : ℕ)
    (h : ProjectiveTargetNormalCoordinateConclusion V y r) :
    ProjectiveCenteredNormalTargetConclusion V y r := by
  classical
  obtain ⟨c, hcr, hc, e, M, hM, H, h0, hD, hlocal, _, _⟩ := h
  let z := M⁻¹ *ᵥ (y ∘ e)
  let C0 := (polynomialLinearChangeEquiv M hM).toRingHom.comp
    (MvPolynomial.rename e.symm).toRingHom
  let P := RingHom.ker (MvPolynomial.aeval (R := ℂ) z).toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime _
  let E := polynomialTranslation z
  obtain ⟨hI, h0', hlocal'⟩ := polynomial_local_generators_actual_centering
    (V.affineIdeal.map C0) P z rfl H hlocal h0
  have hD' := polynomial_normal_firstJet_actual_centering z H hD
  refine ⟨c, hcr, hc, e, M, hM, fun i => E (H i), ?_⟩
  change V.affineIdeal.map (E.toRingHom.comp C0) ≤ _ ∧ _ ∧ _ ∧ _
  rw [← Ideal.map_map]
  exact ⟨hI, h0', hD', hlocal'⟩

/-- Every actual original iterate carries these centered normal target data
at the SAME target as its actual whole ambient fiber. -/
theorem projective_iterates_whole_fibers_centered_normal_targets {n : ℕ}
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
          ProjectiveCenteredNormalTargetConclusion V y r := by
  obtain ⟨r, hrn, hdim, hrank, hiter⟩ :=
    projective_iterates_whole_ambient_fibers_normal_targets f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, ?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p, hp, hgood, hnonempty, hfiber⟩ := hiter k
  refine ⟨p, hp, hgood, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨hgeom, hlinear, hnormal⟩ := hfiber y hy hyp
  exact ⟨hgeom, hlinear, projective_actual_normal_target_centering V y r hnormal⟩

end LinearStudy
