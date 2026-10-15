module
public import Linear.NativeProjectiveChartPullback
public import Linear.ProjectiveSectionDefiningForms
public import Linear.QuotientClosedBaseChange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {n : ℕ}

/-- The ideal of actual homogeneous equations in the original native
degree-zero Proj chart, not in an independently supplied coordinate model. -/
def projectiveNativeChartEquationIdeal {ι : Type*}
    (V : IntegralProjectiveEquations n) (m : ι → ℕ)
    (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Ideal (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact Ideal.span (Set.range (fun i =>
    projectiveNativeChartHomogeneousElement V (m i) (H i) (hH i)))

/-- Actual substituted equations on the original denominator open.
The quotient retains its entire scheme structure, including nilpotents. -/
def projectiveNativeChartPullbackEquationIdeal {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (H : ι → CoordinateRing n) :
    Ideal (Localization.Away (projectiveChartDenominator f V)) :=
  Ideal.span (Set.range (fun i =>
    algebraMap _ (Localization.Away (projectiveChartDenominator f V))
      (Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap (MvPolynomial.aeval f.forms (H i))))))

theorem projectiveNativeChartEquationIdeal_map {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ι → ℕ) (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectiveNativeChartEquationIdeal V m H hH).map
      (projectiveNativeChartPullback f V hq hf hV x hx) =
        projectiveNativeChartPullbackEquationIdeal f V H := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact projectiveNativeChartPullback_map_span f V hq hf hV x hx m H hH

/-- The original-f map of the closed equation quotients. Its existence
is derived from the proved pullback equality of the actual defining ideals. -/
def projectiveNativeChartClosedRingMap {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ι → ℕ) (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ⧸
        projectiveNativeChartEquationIdeal V m H hH) →+*
      (Localization.Away (projectiveChartDenominator f V) ⧸
        projectiveNativeChartPullbackEquationIdeal f V H) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact Ideal.quotientMap (projectiveNativeChartPullbackEquationIdeal f V H)
    (projectiveNativeChartPullback f V hq hf hV x hx)
      ((projectiveNativeChartEquationIdeal_map f V hq hf hV x hx m H hH) ▸
        Ideal.le_comap_map)

theorem projectiveNativeChartClosedRingMap_mk {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ι → ℕ) (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    ∀ a, projectiveNativeChartClosedRingMap f V hq hf hV x hx m H hH
      (Ideal.Quotient.mk (projectiveNativeChartEquationIdeal V m H hH) a) =
      Ideal.Quotient.mk (projectiveNativeChartPullbackEquationIdeal f V H)
        (projectiveNativeChartPullback f V hq hf hV x hx a) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro a
  rfl

/-- The actual closed equation scheme is the fiber product over the
native degree-zero chart ring. This is stronger than equality of point sets. -/
theorem projectiveNativeChartClosed_isPullback_spec {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ι → ℕ) (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (projectiveNativeChartPullbackEquationIdeal f V H))))
      (Spec.map (CommRingCat.ofHom
        (projectiveNativeChartClosedRingMap f V hq hf hV x hx m H hH)))
      (Spec.map (CommRingCat.ofHom (projectiveNativeChartPullback f V hq hf hV x hx)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (projectiveNativeChartEquationIdeal V m H hH)))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact quotientBaseChange_isPullback_of_eq _ _ _
    (projectiveNativeChartEquationIdeal_map f V hq hf hV x hx m H hH)

/-- Transport the proved fiber-product square to the original native
Proj chart and its actual denominator open subscheme. No global gluing or
reducedness assumption is hidden in this statement. -/
theorem projectiveNativeChartClosed_isPullback {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (m : ι → ℕ) (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
        homogeneousQuotientPiece V.ideal.toIdeal 1 :=
      ⟨MvPolynomial.X 0, MvPolynomial.isHomogeneous_X ℂ 0, rfl⟩
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (projectiveNativeChartPullbackEquationIdeal f V H))) ≫
          (projectiveNativeChartDenominatorOpenIso f V x hx).inv)
      (Spec.map (CommRingCat.ofHom
        (projectiveNativeChartClosedRingMap f V hq hf hV x hx m H hH)))
      (projectiveNativeChartDenominatorSchemeMap f V hq hf hV x hx)
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (projectiveNativeChartEquationIdeal V m H hH))) ≫
          (Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).inv) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
      homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0, MvPolynomial.isHomogeneous_X ℂ 0, rfl⟩
  apply (projectiveNativeChartClosed_isPullback_spec f V hq hf hV x hx m H hH).of_iso
    (Iso.refl _) (projectiveNativeChartDenominatorOpenIso f V x hx).symm
    (Iso.refl _) (Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).symm
  · simp
  · simp
  · rw [← projectiveNativeChartSchemeMap_native_comp f V hq hf hV x hx]
    simp [projectiveNativeChartDenominatorSchemeMap]
  · simp

/-- The target zero scheme is a closed subscheme of the original native
Proj chart. The closed immersion is constructed from the actual ideal. -/
theorem projectiveNativeChartClosed_isClosedImmersion {ι : Type*}
    (V : IntegralProjectiveEquations n) (m : ι → ℕ)
    (H : ι → CoordinateRing n) (hH : ∀ i, (H i).IsHomogeneous (m i)) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let hg : Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0) ∈
        homogeneousQuotientPiece V.ideal.toIdeal 1 :=
      ⟨MvPolynomial.X 0, MvPolynomial.isHomogeneous_X ℂ 0, rfl⟩
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (projectiveNativeChartEquationIdeal V m H hH))) ≫
          (Proj.basicOpenIsoSpec _ _ hg Nat.zero_lt_one).inv) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  dsimp only
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (projectiveNativeChartEquationIdeal V m H hH)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/-- The pulled-back zero scheme is closed in the ACTUAL source
denominator open, with its original substituted equations. -/
theorem projectiveNativeChartPulledClosed_isClosedImmersion {ι : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (H : ι → CoordinateRing n) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (projectiveNativeChartPullbackEquationIdeal f V H))) ≫
          (projectiveNativeChartDenominatorOpenIso f V x hx).inv) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (projectiveNativeChartPullbackEquationIdeal f V H)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/-- For the actual linear section constructed from L and w, the source
ideal is the ideal of those SAME linear equations composed with f. -/
theorem projectiveNativeChartPullbackEquationIdeal_linearSection {r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w) =
      Ideal.span (Set.range (fun i =>
        algebraMap _ (Localization.Away (projectiveChartDenominator f V))
          (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap
            (projectiveLinearSectionForms (fun j => MvPolynomial.aeval f.forms (L j)) w i))))) := by
  have he (i : Fin r) :
      MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i) =
        projectiveLinearSectionForms (fun j => MvPolynomial.aeval f.forms (L j)) w i := by
    simp [projectiveLinearSectionForms, linearSectionSourceForms]
  simp only [projectiveNativeChartPullbackEquationIdeal, he]

end LinearStudy
