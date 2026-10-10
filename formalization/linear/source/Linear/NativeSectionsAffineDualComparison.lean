module
public import Linear.NativeBaseSourceChartSections
public import Linear.NativeCoextensionBaseSourceCharts
public import Linear.NativeFullSourceAffinePushforwardDual
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The exact sections-to-affine-dual map, once the original source
chart section map is proved bijective. The original V application derives
this hypothesis. The comparison is the inverse of the ORIGINAL fraction
section map followed by the ORIGINAL affine pushforward functional map. -/
def nativeSectionsAffinePushforwardDualEquiv (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (h : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑
      (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑)
      1 (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha))) :
    nativeProjectiveModuleSections 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
      (op (Proj.basicOpen 𝓑 (algebraMap R S a))) ≃
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).ringCatSheaf) ⟶
        SheafOfModules.unit (Spec (CommRingCat.of
          (HomogeneousLocalization.Away 𝒜 a))).ringCatSheaf) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let f := nativeBaseSourceChartSectionMap 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha
  let e := Equiv.ofBijective f (nativeBaseSourceChartSectionMap_bijective
    𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha h)
  exact e.symm.trans (nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj)

/-- The exact comparison sends the section of an original dual fraction
to the actual original affine pushforward functional. This pins its map,
not merely the existence of some type-level bijection. -/
theorem nativeSectionsAffinePushforwardDualEquiv_section
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (h : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑
      (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑)
      1 (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    nativeSectionsAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj h
      (nativeBaseSourceChartSectionMap 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
        (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha ell) =
      nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  dsimp only
  let f := nativeBaseSourceChartSectionMap 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha
  let e := Equiv.ofBijective f (nativeBaseSourceChartSectionMap_bijective
    𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha h)
  change nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (e.symm (e ell)) = _
  rw [e.symm_apply_apply]
end LinearStudy
