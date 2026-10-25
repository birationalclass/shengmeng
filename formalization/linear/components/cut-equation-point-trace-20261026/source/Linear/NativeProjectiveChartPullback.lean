module
public import Linear.NativeProjectiveChart
public import Linear.ProjectiveChartOpenMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- On the original denominator open, a homogeneous expression pulls back
by the actual defining forms of f, with its actual f0 denominator. -/
theorem projectiveChartOpenMap_homogeneous_pullback
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ℕ) (H : CoordinateRing n) (hH : H.IsHomogeneous m) :
    projectiveChartOpenMap f V hq hf hV x hx
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H)) =
      (IsLocalization.Away.invSelf (projectiveChartDenominator f V))^m *
        algebraMap _ (Localization.Away (projectiveChartDenominator f V))
          (Ideal.Quotient.mk V.affineIdeal
            (affineChartPolynomialMap (MvPolynomial.aeval f.forms H))) := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := Localization.Away (projectiveChartDenominator f V)
  let u : Fin (n+1) → L := fun i => algebraMap B L
    (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms i)))
  let ψ : CoordinateRing n →ₐ[ℂ] L :=
    (IsScalarTower.toAlgHom ℂ B L).comp
      ((Ideal.Quotient.mkₐ ℂ V.affineIdeal).comp affineChartPolynomialMap)
  have he : ψ.comp (MvPolynomial.aeval f.forms) = MvPolynomial.aeval u := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ψ, u]
    rfl
  rw [projectiveChartOpenMap_mk]
  change MvPolynomial.aeval (fun i => u i.succ *
    IsLocalization.Away.invSelf (projectiveChartDenominator f V))
      (affineChartPolynomialMap H) =
    IsLocalization.Away.invSelf (projectiveChartDenominator f V)^m *
      ψ (MvPolynomial.aeval f.forms H)
  rw [← AlgHom.comp_apply,affineChartPolynomialMap_comp_aeval]
  have hu : Fin.cases 1 (fun i => u i.succ *
      IsLocalization.Away.invSelf (projectiveChartDenominator f V)) =
      fun i => IsLocalization.Away.invSelf (projectiveChartDenominator f V) * u i := by
    funext i
    cases i using Fin.cases with
    | zero =>
      change 1 = IsLocalization.Away.invSelf (projectiveChartDenominator f V) *
        algebraMap B L (projectiveChartDenominator f V)
      rw [mul_comm]
      exact (IsLocalization.Away.mul_invSelf _).symm
    | succ i => simp [mul_comm]
  rw [hu,homogeneous_aeval_smul hH,← he]
  rfl

/-- Original-f pullback from the ACTUAL degree-zero native chart ring.
Its source is not an unrelated coordinate model. -/
def projectiveNativeChartPullback
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) →+*
        Localization.Away (projectiveChartDenominator f V) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact (projectiveChartOpenMap f V hq hf hV x hx).toRingHom.comp
    (projectiveNativeChartRingEquiv V x hx).symm.toRingHom

theorem projectiveNativeChartPullback_homogeneous_mk
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ℕ) (H : CoordinateRing n) (hH : H.IsHomogeneous m) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    projectiveNativeChartPullback f V hq hf hV x hx
      (projectiveNativeChartHomogeneousElement V m H hH) =
      (IsLocalization.Away.invSelf (projectiveChartDenominator f V))^m *
        algebraMap _ (Localization.Away (projectiveChartDenominator f V))
          (Ideal.Quotient.mk V.affineIdeal
            (affineChartPolynomialMap (MvPolynomial.aeval f.forms H))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  rw [← projectiveNativeChartRingEquiv_homogeneous_mk V x hx m H hH]
  change projectiveChartOpenMap f V hq hf hV x hx
    ((projectiveNativeChartRingEquiv V x hx).symm
      ((projectiveNativeChartRingEquiv V x hx)
        (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H)))) = _
  rw [RingEquiv.symm_apply_apply]
  exact projectiveChartOpenMap_homogeneous_pullback f V hq hf hV x hx m H hH

open CategoryTheory AlgebraicGeometry

/-- The native chart isomorphism chosen with the original-coordinate
compatibility proved above. -/
def projectiveNativeChartSchemeIso
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (AlgebraicGeometry.Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))).toScheme ≅
        Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  have hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
      homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  exact (AlgebraicGeometry.Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).trans
    (Scheme.Spec.mapIso (projectiveNativeChartRingEquiv V x hx).toCommRingCatIso.op)

/-- The actual localized coordinate pullback induces a scheme morphism
into the original native Proj chart. No global gluing is asserted here. -/
def projectiveNativeChartSchemeMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Spec (CommRingCat.of (Localization.Away (projectiveChartDenominator f V))) ⟶
      (AlgebraicGeometry.Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))).toScheme :=
  Spec.map (CommRingCat.ofHom (projectiveChartOpenMap f V hq hf hV x hx).toRingHom) ≫
    (projectiveNativeChartSchemeIso V x hx).inv

theorem projectiveNativeChartSchemeMap_chart_comp
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    projectiveNativeChartSchemeMap f V hq hf hV x hx ≫
      (projectiveNativeChartSchemeIso V x hx).hom =
        Spec.map (CommRingCat.ofHom (projectiveChartOpenMap f V hq hf hV x hx).toRingHom) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  simp [projectiveNativeChartSchemeMap]

/-- Scheme-defining ideals pull back to the ideal of the actual
substituted homogeneous equations, on the original denominator open.
This is equality of ideals, including nilpotents, not equality of radicals. -/
theorem projectiveNativeChartPullback_map_span {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ι → ℕ) (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (Ideal.span (Set.range (fun i => projectiveNativeChartHomogeneousElement V (m i) (H i) (hH i)))).map
      (projectiveNativeChartPullback f V hq hf hV x hx) =
      Ideal.span (Set.range (fun i =>
        algebraMap _ (Localization.Away (projectiveChartDenominator f V))
          (Ideal.Quotient.mk V.affineIdeal
            (affineChartPolynomialMap (MvPolynomial.aeval f.forms (H i)))))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let ψ := projectiveNativeChartPullback f V hq hf hV x hx
  let a := fun i => projectiveNativeChartHomogeneousElement V (m i) (H i) (hH i)
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := Localization.Away (projectiveChartDenominator f V)
  let b : ι → L := fun i => algebraMap B L
    (Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (H i))))
  have hp (i : ι) : ψ (a i) =
      IsLocalization.Away.invSelf (projectiveChartDenominator f V)^(m i) * b i :=
    projectiveNativeChartPullback_homogeneous_mk f V hq hf hV x hx (m i) (H i) (hH i)
  change (Ideal.span (Set.range a)).map ψ = Ideal.span (Set.range b)
  apply le_antisymm
  · rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨i,rfl⟩,rfl⟩
    rw [hp]
    exact (Ideal.span (Set.range b)).mul_mem_left _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hi : ψ (a i) ∈ (Ideal.span (Set.range a)).map ψ :=
      Ideal.mem_map_of_mem ψ (Ideal.subset_span ⟨i,rfl⟩)
    have he : algebraMap B L (projectiveChartDenominator f V)^(m i) * ψ (a i) = b i := by
      rw [hp,←mul_assoc,←mul_pow,IsLocalization.Away.mul_invSelf,one_pow,one_mul]
    rw [← he]
    exact ((Ideal.span (Set.range a)).map ψ).mul_mem_left _ hi

/-- The actual source is an open subscheme of the original native chart,
defined by the original pullback denominator. -/
def projectiveNativeChartDenominatorOpen
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (AlgebraicGeometry.Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))).toScheme.Opens := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact (projectiveNativeChartSchemeIso V x hx).hom ⁻¹ᵁ
    PrimeSpectrum.basicOpen (projectiveChartDenominator f V)

def projectiveNativeChartDenominatorOpenIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectiveNativeChartDenominatorOpen f V x hx).toScheme ≅
      Spec (CommRingCat.of (Localization.Away (projectiveChartDenominator f V))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact (asIso ((projectiveNativeChartSchemeIso V x hx).hom ∣_
    PrimeSpectrum.basicOpen (projectiveChartDenominator f V))).trans
      (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal))
        (projectiveChartDenominator f V))

/-- Original-f morphism on the actual denominator OPEN SUBSCHEME of the
original native chart. The all-chart global morphism remains to be glued. -/
def projectiveNativeChartDenominatorSchemeMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectiveNativeChartDenominatorOpen f V x hx).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))).toScheme :=
  (projectiveNativeChartDenominatorOpenIso f V x hx).hom ≫
    projectiveNativeChartSchemeMap f V hq hf hV x hx

/-- In the native basic-open chart, the scheme morphism is induced by
the SAME original-f ring pullback whose homogeneous and ideal formulas were proved. -/
theorem projectiveNativeChartSchemeMap_native_comp
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
        homogeneousQuotientPiece V.ideal.toIdeal 1 :=
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    projectiveNativeChartSchemeMap f V hq hf hV x hx ≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).hom =
      Spec.map (CommRingCat.ofHom (projectiveNativeChartPullback f V hq hf hV x hx)) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
      homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  change (Spec.map (CommRingCat.ofHom (projectiveChartOpenMap f V hq hf hV x hx).toRingHom) ≫
    ((Scheme.Spec.mapIso (projectiveNativeChartRingEquiv V x hx).toCommRingCatIso.op).inv ≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).inv)) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).hom = _
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Category.comp_id,Iso.inv_hom_id]
  change Spec.map (CommRingCat.ofHom (projectiveChartOpenMap f V hq hf hV x hx).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (projectiveNativeChartRingEquiv V x hx).symm.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

end LinearStudy
