module
public import Linear.OriginalPushforwardChartLinearityFromSections
public import Linear.NativeNormalizationSourceChartsQuasicoherent
public import Linear.NativeNormalizationDualGlobalHomChartMorphism
public import Linear.NativeNormalizationOriginalChartSectionFormula
public import Linear.NativePushforwardGlobalHomAllSourceFunctions
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.ActualAffineAlgebraDualInternalHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
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
attribute [local irreducible] schemeModuleHomModuleSheaf nativeProjectiveModuleSheaf
  nativeNormalizationProjectiveMap nativeProjectiveChartDegreeZeroSectionMap
  nativeNormalizationDualGlobalHomChartMorphism
  nativeNormalizationPushforwardGlobalHomChartLinearEquiv

/-- The SAME ORIGINAL native-dual/Hom affine-chart morphism preserves
EVERY ACTUAL local source function on EVERY original chart open.
Source-algebra QC and all local source-action laws are DERIVED, not
additional certificates. The native-dual QC and original chart-section
bijection are explicit here; their original-V specialization is separate.
This does not identify the native dual with the genuine canonical sheaf. -/
theorem nativeNormalizationDualGlobalHomChartMorphism_all_source_scalars
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (hq : (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0).IsQuasicoherent) :
    let M := nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let Ai := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a)
    let j := Proj.awayι 𝒜 a ha (by decide)
    let C := nativeNormalizationDualGlobalHomChartMorphism 𝒜 𝓑 a ha hinj hs hq
    ∀ (W : (Spec Ai).Opens) (b : Γ(Proj 𝓑,f ⁻¹ᵁ (j ''ᵁ W)))
      (t : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W)),
    C.app W (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ W) b t) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ W) b (C.app W t) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower K S D := IsScalarTower.of_compHom K S D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  letI : M.IsQuasicoherent := hq
  let f := nativeNormalizationProjectiveMap 𝒜 𝓑
  let F := (Scheme.Modules.pushforward f).obj M
  let P := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := schemeModuleHomModuleSheaf P N
  let Ai := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a)
  let j := Proj.awayι 𝒜 a ha (by decide)
  let U := Proj.basicOpen 𝒜 a
  have hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans
    (Proj.opensRange_awayι 𝒜 a ha (by decide))
  letI : (F.restrict j).IsQuasicoherent :=
    nativeNormalizationDualPushforwardSourceChart_isQuasicoherent 𝒜 𝓑 a ha hs hq
  letI : (P.restrict j).IsQuasicoherent :=
    nativeNormalizationStructureSourceChart_isQuasicoherent 𝒜 𝓑 a ha
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  let Φ := nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs
  dsimp only
  intro W b t
  let C := nativeNormalizationDualGlobalHomChartMorphism 𝒜 𝓑 a ha hinj hs hq
  apply schemeOriginalPushforwardChartMorphism_all_source_scalars_from_sections
    f M N j U hi C (fun x => Φ x)
  · intro b0 t0
    exact nativeNormalizationPushforwardGlobalHomChartLinearEquiv_all_source_functions
      𝒜 𝓑 a ha hinj hs b0 t0
  · intro t0
    exact nativeNormalizationDualGlobalHomChartMorphism_additive_sections 𝒜 𝓑 a ha hinj hs hq t0
end LinearStudy
