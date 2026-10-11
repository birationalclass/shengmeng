module
public import Linear.NativeNormalizationDualGlobalHomChartMorphism
import all Linear.NativeNormalizationDualGlobalHomChartMorphism
public import Linear.ProjectiveNativeSourceDualChartTilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- The actual whole-chart dual/Hom morphism for the SAME original V.
Source quasicoherence and source-section bijectivity are derived from
original finite injective linear projection, rather than assumed. -/
def projectiveNormalization_native_dual_hom_chart_morphism
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :=
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
  let a : A := MvPolynomial.X i
  let ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  let hs := projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
  let hq := projectiveLinearNormalization_native_dual_isFinitePresentation V L hL hfinite
  letI := hq
  nativeNormalizationDualGlobalHomChartMorphism 𝒜 𝓑 a ha
    (IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))) hs
    inferInstance
end LinearStudy
