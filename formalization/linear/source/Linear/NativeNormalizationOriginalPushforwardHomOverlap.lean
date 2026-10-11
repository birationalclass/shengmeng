module
public import Linear.NativeNormalizationPushforwardGlobalHomWeightedLinear
public import Linear.NativeNormalizationPushforwardGlobalHomSourceValues
public import Linear.NativeNormalizationPushforwardGlobalHomWeightedSourceValues
public import Linear.NativeNormalizationDualPushforwardOverlap
public import Linear.NativeNormalizationDualPushforwardDegreeOne
public import Linear.NativeDualGlobalHomOriginalWeightedOverlapRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
/-- Every ACTUAL source-dual pushforward section has the genuine entire
Hom restriction equality under the SAME original comparison maps. The
section bijections are explicit premises here and proved for original V. -/
theorem nativeNormalizationPushforwardGlobalHom_original_overlap_restriction
    [IsDomain R] (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (hs1 : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (hsab : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 2 (algebraMap R S (a*b))
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (SetLike.mul_mem_graded ha hb)))) :
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑
  let hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
  let F := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M
  let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := schemeModuleHomModuleSheaf P Q
  let i := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 (a*b) M
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  letI := nativeNormalizationGlobalWeightedHomChartModule 𝒜 𝓑 2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb)
  let C := nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinja hs1
  let Cab := nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj hsab
  ∀ v : Γ(F,Proj.basicOpen 𝒜 a),
    H.presheaf.map i.op (C v) = Cab (F.presheaf.map i.op v) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑
  let hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
  let F := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M
  let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := schemeModuleHomModuleSheaf P Q
  let i := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 (a*b) M
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  letI := nativeNormalizationGlobalWeightedHomChartModule 𝒜 𝓑 2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb)
  let C := nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinja hs1
  let Cab := nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj hsab
  let theta := nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
    (hR := hR) (hS := hS) 1 a ha
  have htheta := nativeNormalizationPushforwardWeightedChartSectionMap_bijective 𝒜 𝓑 𝒟
    (hR := hR) (hS := hS) 1 a ha hs1
  dsimp only
  intro v
  obtain ⟨ell,rfl⟩ := htheta.surjective v
  let ell0 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)) ell
  have hi := (congrArg C
    (nativeNormalizationPushforwardWeightedChartSectionMap_degree_one_value
      𝒜 𝓑 𝒟 (hR := hR) (hS := hS) a ha ell)).trans
    (nativeNormalizationPushforwardGlobalHomChartLinearEquiv_apply_source_section
      𝒜 𝓑 a ha hinja hs1 ell0)
  let rho := nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hR 1 1 a b ha hb
  have ho := nativeDualGlobalHom_original_weighted_overlap_restriction 𝒜 𝓑 a b ha hb hab hinja hinj ell
  have hr := nativeNormalizationPushforwardWeightedChartSectionMap_original_overlap
    𝒜 𝓑 𝒟 (hR := hR) (hS := hS) 1 1 a b ha hb ell
  have hj := nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv_apply_source_section
    𝒜 𝓑 a b ha hb hab hinja hinj hsab (rho ell)
  exact (congrArg (fun h => H.presheaf.map i.op h) hi).trans
    (ho.trans (hj.symm.trans (congrArg Cab hr.symm)))
end LinearStudy
