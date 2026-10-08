module
public import Linear.ProjectiveWholeFiberLocalMaps
public import Linear.ProjectiveCenteredRationalInvariance
public import Linear.RationalReindexedCenteredLocalMap
public import Linear.PolynomialCoordinatePoints
public import Linear.CenteredCoordinatePointKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the SAME original whole good fiber, derive actual centered rational
local inputs at EVERY source point. The ideal-power sandwich, source and
target prime comparisons and unramification are conclusions, not inputs. -/
theorem projective_whole_fiber_centered_rational_local_inputs
    {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (a : MvPolynomial (Fin n) ℂ)
    (hgood : let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
      let A := Localization.Away (projectiveChartDenominator f V)
      let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
      letI : Algebra B A := φ.toRingHom.toAlgebra
      ∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal a) ∉ P.asIdeal →
        P ∈ Algebra.smoothLocus ℂ A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
        P ∈ Algebra.unramifiedLocus B A)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (ha : MvPolynomial.eval y a ≠ 0)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial τ ℂ) (b : Fin n ≃ τ)
    (M : Matrix τ τ ℂ) (hM : Matrix.det M ≠ 0) :
    let z := M⁻¹ *ᵥ (y ∘ b.symm)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (b.symm j).succ))
    let pL := fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i)
    let pC := fun i => pL i - MvPolynomial.C (z i) * p0
    let I := ((V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom).map
      (polynomialLinearChangeEquiv M hM).toRingHom).map (polynomialTranslation z).toRingHom
    let J := V.affineIdeal.map E.toRingHom
    let Jaway := J.map (algebraMap _ (Localization.Away p0))
    let ψ := rationalPolynomialChartMap p0 pC
    let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : τ → ℂ)).toRingHom
    letI : Q.IsPrime := RingHom.ker_isPrime _
    ∃ (e : ℕ), 0 < e ∧ Jaway ^ e ≤ I.map ψ.toRingHom ∧
      ∃ hhi : I.map ψ.toRingHom ≤ Jaway,
      ∀ x : Fin n → ℂ, x ∈ MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) →
        let x' := fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))
        ∃ hp0 : MvPolynomial.eval x' p0 ≠ 0,
        let P := RingHom.ker (polynomialAwayPointEvaluation x' p0 hp0).toRingHom
        letI : P.IsPrime := RingHom.ker_isPrime _
        ∃ hQP : Q = P.comap ψ.toRingHom,
          (generalPointLocalQuotientPullback I Jaway P Q ψ.toRingHom hQP hhi).FormallyUnramified := by
  intro z p0 p pL pC I J Jaway ψ Q
  letI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨e,he,hlo,hhi⟩ := projective_original_centered_rational_power_sandwich
    f V (Nat.ne_of_gt hq) hV E b M hM z
  refine ⟨e,he,hlo,hhi,?_⟩
  intro x hxF x'
  obtain ⟨hpOld,hQold,huOld⟩ := projective_whole_fiber_actual_local_maps
    f V hq hf hV x0 hx0 a hgood y hy ha x hxF
  let pOld0 := affineChartPolynomialMap (f.forms 0)
  let pOld := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
  let POld := RingHom.ker (polynomialAwayPointEvaluation x pOld0 hpOld).toRingHom
  let QOld := POld.comap (rationalPolynomialChartMap pOld0 pOld).toRingHom
  letI : POld.IsPrime := RingHom.ker_isPrime _
  letI : QOld.IsPrime := inferInstance
  let d := polynomialAwayCoordinateEquiv E pOld0
  let PTrans := POld.comap d.symm.toRingHom
  let QTrans := ((QOld.comap (MvPolynomial.renameEquiv ℂ b).symm.toRingHom).comap
    (polynomialLinearChangeEquiv M hM).symm.toRingHom).comap (polynomialTranslation z).symm.toRingHom
  letI : PTrans.IsPrime := inferInstance
  letI : QTrans.IsPrime := inferInstance
  obtain ⟨hpNew,_,hP⟩ := polynomial_coordinate_away_point_evaluation E x pOld0 hpOld
  let PNew := RingHom.ker (polynomialAwayPointEvaluation x' p0 hpNew).toRingHom
  letI : PNew.IsPrime := RingHom.ker_isPrime _
  have hP' : PTrans = PNew := hP
  have hQold' : QOld = RingHom.ker (MvPolynomial.aeval (R := ℂ) y).toRingHom := hQold
  have hQ : QTrans = Q := by
    change ((QOld.comap _).comap _).comap _ = Q
    rw [hQold']
    exact centered_target_coordinate_point_kernel b M hM y
  obtain ⟨hQPtrans,hhiTrans,huTrans⟩ := rational_reindexed_centered_actual_local_map
    E b M hM z pOld0 pOld V.affineIdeal V.affineIdeal QOld POld rfl
    (projectiveRationalPolynomialChartMap_ideal f V hq hf hV x0 hx0) huOld
  have hQP : Q = PNew.comap ψ.toRingHom := by
    rw [← hQ, ← hP']
    exact hQPtrans
  refine ⟨hpNew,hQP,?_⟩
  exact generalPointLocalQuotientPullback_unramified_transport I Jaway ψ.toRingHom hhi
    PTrans PNew QTrans Q hP' hQ hQPtrans hQP huTrans

end LinearStudy
