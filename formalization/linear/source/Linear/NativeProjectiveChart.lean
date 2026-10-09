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

/-- The actual degree-zero chart ring embeds in the ORIGINAL cone
fraction field via its native localization map. -/
def projectiveNativeChartFractionEmbedding {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) →+*
        FractionRing (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let a₀ : A := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  have ha₀ : a₀ ≠ 0 := by
    intro h
    apply projectiveConeFractionCoordinates_zero_ne_zero V x hx
    change algebraMap A (FractionRing A) a₀ = 0
    rw [h, map_zero]
  exact (awayFractionEmbedding (K := ℂ) a₀ ha₀).toRingHom.comp
    (algebraMap _ (Localization.Away a₀))

/-- The native homogeneous fraction H/X0^m in the original chart. -/
def projectiveNativeChartHomogeneousElement {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℕ) (H : CoordinateRing n)
    (hH : H.IsHomogeneous m) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := homogeneousQuotientPiece V.ideal.toIdeal
  have hgrade : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈ 𝒜 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  exact HomogeneousLocalization.Away.mk 𝒜 hgrade m
    (Ideal.Quotient.mk V.ideal.toIdeal H)
    (by simpa only [smul_eq_mul,mul_one] using
      (show Ideal.Quotient.mk V.ideal.toIdeal H ∈ 𝒜 m from ⟨H,hH,rfl⟩))

theorem projectiveNativeChartFractionEmbedding_injective {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Function.Injective (projectiveNativeChartFractionEmbedding V x hx) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let a₀ : A := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  have ha₀ : a₀ ≠ 0 := by
    intro h
    apply projectiveConeFractionCoordinates_zero_ne_zero V x hx
    change algebraMap A (FractionRing A) a₀ = 0
    rw [h,map_zero]
  intro a b h
  apply HomogeneousLocalization.val_injective (Submonoid.powers a₀)
  apply awayFractionEmbedding_injective (K := ℂ) a₀ ha₀
  exact h

theorem projectiveNativeChartFractionEmbedding_homogeneous_mk {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ℕ) (H : CoordinateRing n) (hH : H.IsHomogeneous m) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    projectiveNativeChartFractionEmbedding V x hx
      (projectiveNativeChartHomogeneousElement V m H hH) =
      (projectiveConeFractionCoordinates V 0)⁻¹^m *
        MvPolynomial.aeval (projectiveConeFractionCoordinates V) H := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let a₀ : A := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let 𝒜 := homogeneousQuotientPiece V.ideal.toIdeal
  let B := Localization.Away a₀
  let z := projectiveConeFractionCoordinates V
  have hn : z 0 ≠ 0 := projectiveConeFractionCoordinates_zero_ne_zero V x hx
  have ha₀ : a₀ ≠ 0 := by
    intro h
    apply hn
    change algebraMap A F a₀ = 0
    rw [h,map_zero]
  let e : B →ₐ[ℂ] F := awayFractionEmbedding a₀ ha₀
  let b := projectiveNativeChartHomogeneousElement V m H hH
  have hd : algebraMap A B (a₀^m) * b.val =
      algebraMap A B (Ideal.Quotient.mk V.ideal.toIdeal H) := by
    dsimp only [b, projectiveNativeChartHomogeneousElement]
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
  have hm : z 0^m * projectiveNativeChartFractionEmbedding V x hx b =
      MvPolynomial.aeval z H := by
    rw [projectiveConeFractionCoordinates_aeval]
    exact he
  apply mul_left_cancel₀ (pow_ne_zero m hn)
  change z 0^m * projectiveNativeChartFractionEmbedding V x hx b =
    z 0^m * ((z 0)⁻¹^m * MvPolynomial.aeval z H)
  rw [hm,← mul_assoc,← mul_pow,mul_inv_cancel₀ hn,one_pow,one_mul]

/-- The actual dehomogenized coordinate quotient equals mathlib's
degree-zero localization of the ORIGINAL graded coordinate quotient.
This is a ring isomorphism, rather than a bijection of closed points. -/
theorem projective_native_chart_ring_equiv_compatible {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    ∃ ec : (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ≃+*
      HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)),
      (projectiveNativeChartFractionEmbedding V x hx).comp ec.toRingHom =
        (projectiveChartCoordinateEmbedding V x hx).toRingHom := by
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
  let θ : T →+* F := projectiveNativeChartFractionEmbedding V x hx
  have hθinj : Function.Injective θ :=
    (awayFractionEmbedding_injective a₀ ha₀).comp
      (HomogeneousLocalization.val_injective (Submonoid.powers a₀))
  have hformula (m : ℕ) (H : CoordinateRing n) (hH : H.IsHomogeneous m) :
      θ (HomogeneousLocalization.Away.mk 𝒜 hgrade m
        (Ideal.Quotient.mk V.ideal.toIdeal H)
        (by simpa only [smul_eq_mul,mul_one] using
          (show Ideal.Quotient.mk V.ideal.toIdeal H ∈ 𝒜 m from ⟨H,hH,rfl⟩))) =
        (z 0)⁻¹^m * MvPolynomial.aeval z H := by
    simpa only [projectiveNativeChartHomogeneousElement] using
      projectiveNativeChartFractionEmbedding_homogeneous_mk V x hx m H hH
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
  let ec := (ep.trans (RingEquiv.subringCongr hrange)).trans et.symm
  refine ⟨ec, ?_⟩
  apply RingHom.ext
  intro a
  change θ (et.symm ((RingEquiv.subringCongr hrange) (ep a))) = φ a
  have h := congrArg Subtype.val
    (et.apply_symm_apply ((RingEquiv.subringCongr hrange) (ep a)))
  change θ (et.symm ((RingEquiv.subringCongr hrange) (ep a))) =
    ((RingEquiv.subringCongr hrange) (ep a)).val at h
  exact h.trans (RingEquiv.coe_subringCongr_apply hrange (ep a))

/-- Retain the original existence interface as a corollary. -/
theorem projective_native_chart_ring_equiv {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Nonempty ((MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ≃+*
      HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨ec, _⟩ := projective_native_chart_ring_equiv_compatible V x hx
  exact ⟨ec⟩

/-- Choose the chart isomorphism together with its original-coordinate
compatibility, rather than choosing an unspecified abstract isomorphism. -/
def projectiveNativeChartRingEquiv {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ≃+*
      HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) :=
  Classical.choose (projective_native_chart_ring_equiv_compatible V x hx)

theorem projectiveNativeChartRingEquiv_fraction_comp {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectiveNativeChartFractionEmbedding V x hx).comp
      (projectiveNativeChartRingEquiv V x hx).toRingHom =
        (projectiveChartCoordinateEmbedding V x hx).toRingHom :=
  Classical.choose_spec (projective_native_chart_ring_equiv_compatible V x hx)


/-- The canonical isomorphism sends dehomogenization to the actual
homogeneous fraction, including the original numerator and denominator. -/
theorem projectiveNativeChartRingEquiv_homogeneous_mk {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ℕ) (H : CoordinateRing n) (hH : H.IsHomogeneous m) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    projectiveNativeChartRingEquiv V x hx
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H)) =
        projectiveNativeChartHomogeneousElement V m H hH := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  apply projectiveNativeChartFractionEmbedding_injective V x hx
  have h := RingHom.congr_fun (projectiveNativeChartRingEquiv_fraction_comp V x hx)
    (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H))
  rw [RingHom.comp_apply] at h
  change projectiveNativeChartFractionEmbedding V x hx
    (projectiveNativeChartRingEquiv V x hx
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H))) =
    projectiveChartCoordinateEmbedding V x hx
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H)) at h
  rw [h,projectiveChartCoordinateEmbedding_mk,
    coordinateRatioPolynomialMap_homogeneous _
      (projectiveConeFractionCoordinates_zero_ne_zero V x hx) H hH,
    projectiveNativeChartFractionEmbedding_homogeneous_mk]

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
