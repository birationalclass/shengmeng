module
public import Linear.NativeNormalizationPushforwardGlobalHomChartLinear
public import Linear.ProjectiveNativeDualChartSectionsBijective
public import Linear.NativeAffineInternalHomLinear
public import Linear.NativeCoextensionBaseSourceCharts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- For the SAME ORIGINAL V and finite injective linear normalization,
actual sections of the global finite-dual pushforward are linearly equivalent
to ACTUAL global internal Hom chart sections. Source-section bijectivity is
derived from the original normalization, not given as a chart certificate. -/
def projectiveNormalization_native_global_chart_duality_linearEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
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
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
    letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 (MvPolynomial.X i) M
    let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i)
    Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
      Proj.basicOpen 𝒜 (MvPolynomial.X i))
      ≃ₗ[HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)]
        Γ(schemeModuleHomModuleSheaf P N,Proj.basicOpen 𝒜 (MvPolynomial.X i)) := by
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
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  letI : IsScalarTower A B D := IsScalarTower.of_compHom A B D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let a : A := MvPolynomial.X i
  have ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  have hs := projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
  dsimp only
  exact nativeNormalizationPushforwardGlobalHomChartLinearEquiv (K := ℂ) (R := A) (S := B)
    𝒜 𝓑 a ha
    (IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))) hs


end LinearStudy
