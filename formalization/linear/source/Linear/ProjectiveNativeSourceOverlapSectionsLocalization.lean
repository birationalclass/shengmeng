module
public import Linear.NativeFiniteGradedChartOverlapLocalization
public import Linear.NativeSourceSpecChartTilde
public import Linear.ProjectiveNativeDualChartSectionsBijective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
variable {n r : ℕ}

/-- Genuine restriction of the SAME original native dual on each source coordinate overlap is module localization. Its quasicoherence is derived from the original finite normalization. -/
theorem projectiveNormalization_native_source_overlap_sections_isLocalizedModule
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i j : Fin (r+1)) :
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
    letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    ∀ ha : φ (MvPolynomial.X i) ∈ 𝓑 1,
    ∀ hb : φ (MvPolynomial.X j) ∈ 𝓑 1,
    let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
    let Q := F.restrict (Proj.awayι 𝓑 (φ (MvPolynomial.X i)) ha (by decide))
    let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
    IsLocalizedModule (Submonoid.powers t)
      ((modulesSpecToSheaf.obj Q).obj.map (PrimeSpectrum.basicOpen t).leTop.op).hom := by
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
  letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  letI : F.IsFinitePresentation :=
    projectiveLinearNormalization_native_dual_isFinitePresentation V L hL hfinite
  letI : F.IsQuasicoherent := inferInstance
  dsimp only
  intro ha hb
  let Q := F.restrict (Proj.awayι 𝓑 (φ (MvPolynomial.X i)) ha (by decide))
  letI : Q.IsQuasicoherent := inferInstance
  exact (isIso_fromTildeΓ_iff_isLocalizing Q).mp inferInstance
    (HomogeneousLocalization.Away.isLocalizationElem ha hb)
end LinearStudy
