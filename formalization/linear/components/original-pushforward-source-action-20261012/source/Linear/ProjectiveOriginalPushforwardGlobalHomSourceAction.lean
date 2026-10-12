module
public import Linear.NativePushforwardGlobalHomOriginalSourceAction
public import Linear.ProjectiveNativeDualChartSectionsBijective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 350000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveChartDegreeZeroSectionMap
  nativeNormalizationPushforwardGlobalHomChartLinearEquiv schemeModuleHomModuleSheaf
variable {n r : ℕ}

/-- For the ORIGINAL integral projective equations and SAME finite
injective linear normalization, the ORIGINAL pushforward/global-Hom
comparison on EVERY coordinate chart preserves source multiplication
on EVERY actual pushforward section. Both localization injectivity and
the native chart-section bijection are DERIVED, not extra hypotheses.
This does not identify the native dual with the canonical sheaf. -/
theorem projectiveNormalization_original_pushforward_global_hom_source_action
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
    letI : Module.Finite A B := hfinite
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    ∀ i : Fin (r+1),
    let a := MvPolynomial.X i
    let ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
    let hi : Function.Injective (algebraMap A (Localization.Away a)) :=
      IsLocalization.injective (Localization.Away a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))
    let hs := projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
    let U := Proj.basicOpen 𝒜 a
    ∀ (b : HomogeneousLocalization.Away 𝓑 (algebraMap A B a))
      (t : Γ((Scheme.Modules.pushforward f).obj M,U)),
    let sb : Γ(Proj 𝓑,f ⁻¹ᵁ U) := by
      change Γ(Proj 𝓑,(nativeNormalizationProjectiveMap 𝒜 𝓑) ⁻¹ᵁ (Proj.basicOpen 𝒜 a))
      rw [nativeNormalizationProjectiveMap_preimage_basicOpen]
      exact (Proj.awayToSection 𝓑 (algebraMap A B a)) b
    nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hi hs
      (schemePushforwardOriginalSourceActionSection f M U sb t) =
    schemePushforwardHomSourceActionSection f N U sb
      (nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hi hs t) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite A B := hfinite
  dsimp only
  intro i b t
  exact nativeNormalizationPushforwardGlobalHomChartLinearEquiv_original_source_action
    𝒜 𝓑 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (MvPolynomial.isHomogeneous_X ℂ i))) b t
end LinearStudy
