module
public import Linear.NativeNormalizationDualChartMorphismAllSourceScalars
public import Linear.ProjectiveNativeDualChartSectionsBijective
public import Linear.ProjectiveDualNativeQuasicoherent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveChartDegreeZeroSectionMap
  nativeNormalizationProjectiveMap nativeNormalizationDualGlobalHomChartMorphism
  nativeNormalizationPushforwardGlobalHomChartLinearEquiv schemeModuleHomModuleSheaf
variable {n r : ℕ}

/-- For the ORIGINAL integral projective equations V and SAME finite
injective linear normalization, the SAME original native-dual/Hom chart
morphism preserves EVERY local source function and EVERY local section
on EVERY open in EVERY coordinate chart. Localization injectivity,
native-dual QC and the actual chart-section bijection are ALL DERIVED.
No local action/compatibility/QC certificate is added to the original V.
This does not assert the genuine normalized-dualizing H^-r identification. -/
theorem projectiveNormalization_original_dual_chart_all_source_scalars
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
    let M := nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
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
    let hq := projectiveLinearNormalization_native_dual_isQuasicoherent V L hL hfinite
    let Ai := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a)
    let j := Proj.awayι 𝒜 a ha (by decide)
    let C := nativeNormalizationDualGlobalHomChartMorphism 𝒜 𝓑 a ha hi hs hq
    ∀ (W : (Spec Ai).Opens) (b : Γ(Proj 𝓑,f ⁻¹ᵁ (j ''ᵁ W)))
      (t : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W)),
    C.app W (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ W) b t) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ W) b (C.app W t) := by
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
  -- Apply the already proved whole local statement as a function;
  -- avoid expanding every section type under three introductions.
  exact fun i => nativeNormalizationDualGlobalHomChartMorphism_all_source_scalars
    𝒜 𝓑 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (MvPolynomial.isHomogeneous_X ℂ i)))
    (projectiveLinearNormalization_native_dual_isQuasicoherent V L hL hfinite)
end LinearStudy
