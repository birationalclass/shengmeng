module
public import Linear.ActualAffineAlgebraDualValueNaturality
public import Linear.NativeNormalizationWeightedOverlapDualValues
public import Linear.NormalizationHomogeneousAffineDualOverlapValues
public import Linear.NativeDualFullSourceChartEquiv
public import Linear.CoextensionBaseGradeCompatibility
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
public import Mathlib.Algebra.Module.Torsion.Pi
public import Linear.NativeGlobalHomWeightedOverlapEvaluation
public import Linear.NativeDualGlobalHomWeightedOverlapValues
public import Linear.NativeWeightedAffineInternalHomValueNaturality
public import Linear.NativeWeightedHomDegreeOneValues
public import Linear.NativeActualAffineOverlapHomOriginalElementsExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  normalizationHomogeneousSourceChartAlgebra
theorem nativeDualGlobalHom_original_weighted_overlap_restriction [IsDomain R]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (ell : nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 1 a)
    :
  let Ai := HomogeneousLocalization.Away 𝒜 a
  let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let N := nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)
  letI := nativeCoextensionNormalizationBase_isTorsionFree (R := R) (S := S)
  letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
  letI : Algebra Ai Aij := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI : IsScalarTower Ai Aij N := IsScalarTower.of_compHom Ai Aij N
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  let powers := Submonoid.powers t
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := nativeGradedDegreeOneOverlap_isLocalizedModule 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb hab
  let rhoD := nativeGradedDegreeOneOverlapLinearMap 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb
  let E1 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)).trans
    (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinja)

  let Bi := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let Bij := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
  let phi : Ai →+* Aij := HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
  let gamma : Bi →+* Bij := HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb) (map_mul (algebraMap R S) a b)
  let fi : Bi →ₗ[Ai] Ai := E1 ell
  let fij : Bij →ₗ[Aij] Aij := nativeNormalizationWeightedOverlapDualLinearEquiv
    𝒜 𝓑 a b ha hb hab hinja hinj
      (nativeGradedModuleWeightedOverlapMap 𝒜 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) 1 1 a b ha hb ell)
    let PA := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap Ai Bi)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of Bi)).ringCatSheaf)
    let QA : (Spec (CommRingCat.of Ai)).Modules := SheafOfModules.unit (Spec (CommRingCat.of Ai)).ringCatSheaf
    let PT := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap Aij Bij)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of Bij)).ringCatSheaf)
    let QT : (Spec (CommRingCat.of Aij)).Modules := SheafOfModules.unit (Spec (CommRingCat.of Aij)).ringCatSheaf
    let eA : tilde (R := CommRingCat.of Ai) (ModuleCat.of Ai Bi) ≅ PA := actualAffineAlgebraStructurePushforwardIso
    let eT : tilde (R := CommRingCat.of Aij) (ModuleCat.of Aij Bij) ≅ PT := actualAffineAlgebraStructurePushforwardIso
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let h := nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinja
      ((LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)) ell)
    (schemeModuleHomModuleSheaf M Q).presheaf.map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op h =
      nativeDualGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj
        (nativeGradedModuleWeightedOverlapMap 𝒜 (coextensionGradedPiece 𝒜 𝓑)
          (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) 1 1 a b ha hb ell) := by
  let Ai := HomogeneousLocalization.Away 𝒜 a
  let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let N := nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)
  letI := nativeCoextensionNormalizationBase_isTorsionFree (R := R) (S := S)
  letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
  letI : Algebra Ai Aij := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI : IsScalarTower Ai Aij N := IsScalarTower.of_compHom Ai Aij N
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  let powers := Submonoid.powers t
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := nativeGradedDegreeOneOverlap_isLocalizedModule 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb hab
  let rhoD := nativeGradedDegreeOneOverlapLinearMap 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb
  let E1 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)).trans
    (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinja)

  let Bi := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let Bij := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
  let phi : Ai →+* Aij := HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
  let gamma : Bi →+* Bij := HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb) (map_mul (algebraMap R S) a b)
  let fi : Bi →ₗ[Ai] Ai := E1 ell
  let fij : Bij →ₗ[Aij] Aij := nativeNormalizationWeightedOverlapDualLinearEquiv
    𝒜 𝓑 a b ha hb hab hinja hinj
      (nativeGradedModuleWeightedOverlapMap 𝒜 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) 1 1 a b ha hb ell)
  let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let ell0 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)) ell
  let h := nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinja ell0
  let i := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
  let G := nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv
    𝒜 𝓑 2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb)
  dsimp only
  apply G.injective
  apply nativeActualAffineOverlapHom_original_elements_ext 𝒜 𝓑 a b ha hb
  intro x
  have h1 := nativeNormalizationGlobalWeightedHom_original_overlap_values 𝒜 𝓑 a b ha hb h x
  have h2 := nativeWeightedAffineInternalHomValueNaturality 𝒜 𝓑 a b ha hb hab hinja hinj ell x
  have hi := nativeDualGlobalHomChartLinearEquiv_affine_section_value 𝒜 𝓑 a ha hinja ell0
  have hj := nativeDualGlobalHomWeightedOverlapLinearEquiv_affine_section_value 𝒜 𝓑
    a b ha hb hab hinja hinj
    (nativeGradedModuleWeightedOverlapMap 𝒜 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) 1 1 a b ha hb ell)
  let PA := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap Ai Bi)))).obj
    (SheafOfModules.unit (Spec (CommRingCat.of Bi)).ringCatSheaf)
  let QA : (Spec (CommRingCat.of Ai)).Modules := SheafOfModules.unit (Spec (CommRingCat.of Ai)).ringCatSheaf
  let eA := actualAffineAlgebraStructurePushforwardIso (A := Ai) (B := Bi)
  have hv := congrArg (fun z => (Spec.map (CommRingCat.ofHom phi)).appTop
    (schemeModuleHomSectionEvaluation PA QA ⊤ z
      (eA.hom.app ⊤ (tilde.toOpen (R := CommRingCat.of Ai) (ModuleCat.of Ai Bi) ⊤ x)))) hi
  let PT := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap Aij Bij)))).obj
    (SheafOfModules.unit (Spec (CommRingCat.of Bij)).ringCatSheaf)
  let QT : (Spec (CommRingCat.of Aij)).Modules := SheafOfModules.unit (Spec (CommRingCat.of Aij)).ringCatSheaf
  let eT := actualAffineAlgebraStructurePushforwardIso (A := Aij) (B := Bij)
  have hv' := congrArg (fun z => schemeModuleHomSectionEvaluation PT QT ⊤ z
    (eT.hom.app ⊤ (tilde.toOpen (R := CommRingCat.of Aij) (ModuleCat.of Aij Bij) ⊤ (gamma x)))) hj
  exact (h1.trans hv).trans (h2.symm.trans hv'.symm)
end LinearStudy
