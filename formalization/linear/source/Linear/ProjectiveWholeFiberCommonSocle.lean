module
public import Linear.ProjectiveOriginalFiberLocalSocle
public import Linear.ProjectiveWholeFiberCommonCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4800000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

theorem local_generators_at_equal_primes {R ι : Type*} [CommRing R]
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q) (G : ι → R)
    (hs : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (G i))) := by
  subst Q
  exact hs

/-- Explicit OUTPUT on the original whole fiber, retaining actual linear
source and target coordinates and the SAME polynomial normal Jacobian. -/
def ProjectiveWholeFiberCommonSocleConclusion {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (r : ℕ) : Prop :=
    ∃ c : ℕ, c = n-r ∧ 0 < c ∧
      ∃ (eS : (Fin r ⊕ Fin c) ≃ Fin n)
        (MS : Matrix (Fin n) (Fin n) ℂ) (hMS : Matrix.det MS ≠ 0)
        (eT : (Fin r ⊕ Fin c) ≃ Fin n)
        (MT : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) ℂ) (hMT : Matrix.det MT ≠ 0),
      let E := (polynomialLinearChangeEquiv MS hMS).trans (MvPolynomial.renameEquiv ℂ eS.symm)
      let z := MT⁻¹ *ᵥ (y ∘ eT)
      let p0 := E (affineChartPolynomialMap (f.forms 0))
      let p : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
        fun j => E (affineChartPolynomialMap (f.forms (eT j).succ))
      let pC : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
        fun i => MvPolynomial.aeval p ((MT⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
      let A := MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range pC)
      let Θ : MvPolynomial (Fin r ⊕ Fin c) ℂ :=
        Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (pC (Sum.inr i)))
      Module.Finite ℂ A ∧
        ∀ x : MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y),
          let x' := fun j => MvPolynomial.eval x.val (E.symm (MvPolynomial.X j))
          ∃ q : A →ₐ[ℂ] ℂ,
            x' = (fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
            letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
            let t := algebraMap A (Localization.AtPrime (RingHom.ker q.toRingHom))
              (Ideal.Quotient.mk _ Θ)
            (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
              Ideal.span {t} ∧ t ≠ 0

/-- Insert the constructed ORIGINAL common source and centered target normal
coordinates. No normal generators, Jacobian socles or local map comparisons
are extra inputs beyond the previously proved actual geometric outputs. -/
theorem projective_actual_whole_fiber_common_socle
    {n r : ℕ} (hr : 0 < r)
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
    (hcoords : ProjectiveWholeFiberCommonCoordinateConclusion f V y hy r)
    (htarget : ProjectiveCenteredNormalTargetConclusion V y r) :
    ProjectiveWholeFiberCommonSocleConclusion f V y r := by
  classical
  let S := MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)
  let hx : ∀ x : S, normalizedProjectivePoint x.val ∈ V.zeroSet :=
    fun x => (projectiveAffineFiberIdeal_point f V y x.val x.property).1
  obtain ⟨hS,hSne,_,_,_,c,hcr,hpres⟩ := hcoords
  obtain ⟨hc,eS,MS,hMS,G,hG,hJac,hs,_⟩ := hpres
  obtain ⟨cT,hcTr,hcT,eT,MT,hMT,H,hIQ,hH0,hHD,ht⟩ := htarget
  have hcEq : cT = c := hcTr.trans hcr.symm
  clear hcTr
  subst cT
  let E := (polynomialLinearChangeEquiv MS hMS).trans (MvPolynomial.renameEquiv ℂ eS.symm)
  have hpoint (x : S) : (fun j => MvPolynomial.eval x.val (E.symm (MvPolynomial.X j))) =
      (MS⁻¹ *ᵥ x.val) ∘ eS := linear_reindexed_actual_source_point MS hMS eS x.val
  have hG' : ∀ x i, MvPolynomial.eval
      (fun j => MvPolynomial.eval x.val (E.symm (MvPolynomial.X j))) (E (G x i)) = 0 := by
    intro x i
    rw [hpoint]
    exact hG x i
  have hJac' : ∀ x : S, IsUnit (Matrix.det (fun i j => MvPolynomial.eval
      (fun k => MvPolynomial.eval x.val (E.symm (MvPolynomial.X k)))
        (MvPolynomial.pderiv (Sum.inr j) (E (G x i))))) := by
    intro x
    rw [hpoint]
    exact hJac x
  have hs' (x : S) :
      let P := RingHom.ker (MvPolynomial.aeval (R := ℂ) x.val).toRingHom
      letI : P.IsPrime := RingHom.ker_isPrime _
      V.affineIdeal.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G x i))) := by
    let P := (V.affinePoint x.val (hx x)).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
    let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) x.val).toRingHom
    letI : P.IsPrime := inferInstance
    letI : Q.IsPrime := RingHom.ker_isPrime _
    exact local_generators_at_equal_primes V.affineIdeal P Q
      (V.affinePointIdeal_comap x.val (hx x)) (G x) (hs x)
  have ht' :
      let z := MT⁻¹ *ᵥ (y ∘ eT)
      let I := ((V.affineIdeal.map (MvPolynomial.renameEquiv ℂ eT.symm).toRingHom).map
        (polynomialLinearChangeEquiv MT hMT).toRingHom).map (polynomialTranslation z).toRingHom
      let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin r ⊕ Fin c → ℂ)).toRingHom
      letI : Q.IsPrime := RingHom.ker_isPrime _
      I ≤ Q ∧ I.map (algebraMap _ (Localization.AtPrime Q)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))) := by
    have hRename : (MvPolynomial.renameEquiv ℂ eT.symm).toRingHom =
        (MvPolynomial.rename eT.symm).toRingHom := by
      apply RingHom.ext
      intro F
      change (MvPolynomial.renameEquiv ℂ eT.symm) F = MvPolynomial.rename eT.symm F
      exact MvPolynomial.renameEquiv_apply ℂ eT.symm F
    exact ⟨by simpa only [Ideal.map_map,hRename] using hIQ,
      by simpa only [Ideal.map_map,hRename] using ht⟩
  refine ⟨c,hcr,hc,eS,MS,hMS,eT,MT,hMT,?_⟩
  exact projective_original_whole_fiber_local_socles hr hc f V hq hf hV x0 hx0
    a hgood y hy ha E eT.symm MT hMT G hG' hJac' hs' H hH0 hHD ht'

/-- For EVERY original iterate construct a nonempty good target open, and
derive the SAME polynomial normal Jacobian socle at EVERY original source
point. Positive actual chart dimension is stated explicitly; no socle or
normal-coordinate conditions are assumed. This is still ONE whole fiber,
not the simultaneous Bertini union or the global homogeneous relation. -/
theorem projective_iterates_whole_fibers_common_jacobian_socles {n : ℕ}
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
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 → 0 < r →
          ProjectiveWholeAmbientFiberConclusion F V y hy r ∧
            ProjectiveWholeFiberCommonSocleConclusion F V y r := by
  obtain ⟨r,hrn,hdim,hrank,hiter⟩ := projective_iterates_whole_fibers_actual_local_maps
    f V hq hf hV hproper x0 hx0
  refine ⟨r,hrn,hdim,hrank,?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p,hp,hgood,hnonempty,hfiber⟩ := hiter k
  refine ⟨p,hp,hnonempty,?_⟩
  intro y hy hyp hr
  obtain ⟨hgeom,htarget,_⟩ := hfiber y hy hyp
  exact ⟨hgeom,projective_actual_whole_fiber_common_socle hr F V (f.iterate_degree_pos hq k)
    (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k)
    x0 hx0 p hgood y hy hyp hgeom.1 htarget⟩

end LinearStudy
