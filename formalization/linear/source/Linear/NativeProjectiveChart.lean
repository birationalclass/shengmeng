module
public import Linear.HomogeneousCoordinateGrading
public import Linear.ProjectiveChartFractionField
public import Linear.AwayFractionEmbedding
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual dehomogenized coordinate quotient equals mathlib's
degree-zero localization of the ORIGINAL graded coordinate quotient.
This is a ring isomorphism, rather than a bijection of closed points. -/
theorem projective_native_chart_ring_equiv {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Nonempty ((MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ≃+*
      HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))) := by
  classical
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let a₀ : A := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let 𝒜 := homogeneousQuotientPiece V.ideal.toIdeal
  let T := HomogeneousLocalization.Away 𝒜 a₀
  let B := Localization.Away a₀
  let z := projectiveConeFractionCoordinates V
  have hn : z 0 ≠ 0 := projectiveConeFractionCoordinates_zero_ne_zero V x hx
  have ha₀ : a₀ ≠ 0 := by
    intro h
    apply hn
    change algebraMap A F a₀=0
    rw [h,map_zero]
  have hgrade : a₀ ∈ 𝒜 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let e : B →ₐ[ℂ] F := awayFractionEmbedding a₀ ha₀
  let θ : T →+* F := e.toRingHom.comp (algebraMap T B)
  have hθinj : Function.Injective θ :=
    (awayFractionEmbedding_injective a₀ ha₀).comp
      (HomogeneousLocalization.val_injective (Submonoid.powers a₀))
  have hformula (m : ℕ) (H : CoordinateRing n) (hH : H.IsHomogeneous m) :
      θ (HomogeneousLocalization.Away.mk 𝒜 hgrade m
        (Ideal.Quotient.mk V.ideal.toIdeal H)
        (by simpa only [smul_eq_mul,mul_one] using
          (show Ideal.Quotient.mk V.ideal.toIdeal H ∈ 𝒜 m from ⟨H,hH,rfl⟩))) =
        (z 0)⁻¹^m * MvPolynomial.aeval z H := by
    let b : T := HomogeneousLocalization.Away.mk 𝒜 hgrade m
      (Ideal.Quotient.mk V.ideal.toIdeal H)
      (by simpa only [smul_eq_mul,mul_one] using
        (show Ideal.Quotient.mk V.ideal.toIdeal H ∈ 𝒜 m from ⟨H,hH,rfl⟩))
    have hd : algebraMap A B (a₀^m) * b.val =
        algebraMap A B (Ideal.Quotient.mk V.ideal.toIdeal H) := by
      dsimp only [b]
      rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
      exact IsLocalization.mk'_spec' B _ _
    have he := congrArg e hd
    change awayFractionEmbedding (K:=ℂ) a₀ ha₀
      (algebraMap A B (a₀^m) * b.val) =
        awayFractionEmbedding (K:=ℂ) a₀ ha₀
          (algebraMap A B (Ideal.Quotient.mk V.ideal.toIdeal H)) at he
    rw [map_mul,awayFractionEmbedding_algebraMap a₀ ha₀ (a₀^m),
      awayFractionEmbedding_algebraMap a₀ ha₀ (Ideal.Quotient.mk V.ideal.toIdeal H),
      map_pow] at he
    have hm : z 0^m * θ b = MvPolynomial.aeval z H := by
      rw [projectiveConeFractionCoordinates_aeval]
      exact he
    apply mul_left_cancel₀ (pow_ne_zero m hn)
    change z 0^m * θ b = z 0^m * ((z 0)⁻¹^m * MvPolynomial.aeval z H)
    rw [hm,← mul_assoc,← mul_pow,mul_inv_cancel₀ hn,one_pow,one_mul]
  let φ := (projectiveChartCoordinateEmbedding V x hx).toRingHom
  have hpoly (P : MvPolynomial (Fin n) ℂ) :
      coordinateRatioPolynomialMap z P ∈ θ.range := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      refine ⟨HomogeneousLocalization.Away.mk 𝒜 hgrade 0
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.C c))
        (by simpa only [smul_eq_mul,mul_one] using
          (show Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.C c) ∈ 𝒜 0 from
            ⟨MvPolynomial.C c,MvPolynomial.isHomogeneous_C (Fin (n+1)) c,rfl⟩)),?_⟩
      rw [hformula 0 _ (MvPolynomial.isHomogeneous_C (Fin (n+1)) c)]
      simp [coordinateRatioPolynomialMap]
    | add P Q hP hQ =>
      rw [map_add]
      exact θ.range.add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul]
      apply θ.range.mul_mem hP
      refine ⟨HomogeneousLocalization.Away.mk 𝒜 hgrade 1
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.succ))
        (by simpa only [smul_eq_mul,mul_one] using
          (show Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.succ) ∈ 𝒜 1 from
            ⟨MvPolynomial.X i.succ,MvPolynomial.isHomogeneous_X ℂ i.succ,rfl⟩)),?_⟩
      rw [hformula 1 _ (MvPolynomial.isHomogeneous_X ℂ i.succ)]
      simp [coordinateRatioPolynomialMap,div_eq_mul_inv,mul_comm]
  have hrange : φ.range=θ.range := by
    ext u
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
      change projectiveChartCoordinateEmbedding V x hx (Ideal.Quotient.mk V.affineIdeal P) ∈ _
      rw [projectiveChartCoordinateEmbedding_mk]
      exact hpoly P
    · rintro ⟨b,rfl⟩
      obtain ⟨m,a,ha,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hgrade b
      have ham : a ∈ 𝒜 m := by simpa only [smul_eq_mul,mul_one] using ha
      obtain ⟨H,hH,rfl⟩ := (homogeneousQuotientPiece_mem_iff V.ideal.toIdeal m a).mp ham
      refine ⟨Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H),?_⟩
      change projectiveChartCoordinateEmbedding V x hx
        (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H)) = _
      rw [projectiveChartCoordinateEmbedding_mk,
        coordinateRatioPolynomialMap_homogeneous z hn H hH,hformula m H hH]
  let ep : (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ≃+* φ.range :=
    RingEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b hab => projectiveChartCoordinateEmbedding_injective V x hx
        (congrArg Subtype.val hab),φ.rangeRestrict_surjective⟩
  let et : T ≃+* θ.range := RingEquiv.ofBijective θ.rangeRestrict
    ⟨fun a b hab => hθinj (congrArg Subtype.val hab),θ.rangeRestrict_surjective⟩
  exact ⟨(ep.trans (RingEquiv.subringCongr hrange)).trans et.symm⟩

open CategoryTheory AlgebraicGeometry

/-- The corresponding actual open subscheme of Proj is the spectrum
of the original affine coordinate quotient, not just the same point set. -/
theorem projective_native_chart_scheme_iso {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Nonempty ((AlgebraicGeometry.Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))).toScheme ≅
        Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨e⟩ := projective_native_chart_ring_equiv V x hx
  have hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
      homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  exact ⟨(AlgebraicGeometry.Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).trans
    (Scheme.Spec.mapIso e.toCommRingCatIso.op)⟩

end LinearStudy
