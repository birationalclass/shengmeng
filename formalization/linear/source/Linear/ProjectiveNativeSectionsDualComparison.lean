module
public import Linear.NativeSectionsAffineDualComparison
public import Linear.ProjectiveNativeBaseDualSections
public import Linear.ProjectiveNativeAffinePushforwardDuality
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

/-- The ORIGINAL V has a specified sections-to-affine-pushforward-dual
comparison. Source chart surjectivity and all grading hypotheses are proved
from its finite injective linear normalization, not supplied as certificates.
The map is the inverse of its actual dual fraction section map followed by
the actual affine pushforward functional comparison. -/
def projectiveNormalization_native_sections_affine_dual_equiv
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
    let Aᵢ := HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)
    let Bᵢ := HomogeneousLocalization.Away 𝓑 (algebraMap A B (MvPolynomial.X i))
    let g := Spec.map (CommRingCat.ofHom (algebraMap Aᵢ Bᵢ))
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    nativeProjectiveModuleSections 𝓑 𝒟 hD 0
        (op (Proj.basicOpen 𝓑 (φ (MvPolynomial.X i)))) ≃
        ((Scheme.Modules.pushforward g).obj
          (SheafOfModules.unit (Spec (CommRingCat.of Bᵢ)).ringCatSheaf) ⟶
          SheafOfModules.unit (Spec (CommRingCat.of Aᵢ)).ringCatSheaf) := by
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
  let a : A := MvPolynomial.X i
  have ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  have haS : φ a ∈ 𝓑 1 := (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha
  exact nativeSectionsAffinePushforwardDualEquiv 𝒜 𝓑 a ha
    (IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i haS)

/-- On the ORIGINAL V, the specified comparison sends each actual dual
fraction section to its original affine pushforward functional. -/
theorem projectiveNormalization_native_sections_affine_dual_equiv_section
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
    let Aᵢ := HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)
    let Bᵢ := HomogeneousLocalization.Away 𝓑 (algebraMap A B (MvPolynomial.X i))
    let g := Spec.map (CommRingCat.ofHom (algebraMap Aᵢ Bᵢ))
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    letI : IsScalarTower A B D := IsScalarTower.of_compHom A B D
    ∀ ell : nativeGradedModuleAwayZero 𝒜 𝒟 (MvPolynomial.X i),
      projectiveNormalization_native_sections_affine_dual_equiv V L hL hinj hfinite i
        (nativeBaseSourceChartSectionMap 𝒜 𝓑 𝒟
          (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
          (hS := hD) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) ell) =
        nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X ℂ i)
          (IsLocalization.injective (Localization.Away (MvPolynomial.X i))
            (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))) ell := by
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
  let a : A := MvPolynomial.X i
  have ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  have haS : φ a ∈ 𝓑 1 := (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  letI : IsScalarTower A B D := IsScalarTower.of_compHom A B D
  dsimp only
  intro ell
  exact nativeSectionsAffinePushforwardDualEquiv_section 𝒜 𝓑 a ha
    (IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i haS) ell
end LinearStudy
