module
public import Linear.NativeNormalizationPushforwardChartModules
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The actual GLOBAL normalization structure sheaf pushforward,
on its ORIGINAL affine chart, is the SAME affine chart structure
sheaf pushforward used in the verified affine Hom dual comparison. -/
def nativeNormalizationPushforwardStructureChartModuleIso
    (a : R) (ha : a ∈ 𝒜 1) :
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).restrict
      (Proj.awayι 𝒜 a ha (by decide)) ≅
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).ringCatSheaf) :=
  nativeNormalizationPushforwardChartModuleIso 𝒜 𝓑 a ha _ ≪≫
    (Scheme.Modules.pushforward _).mapIso
      (Scheme.Modules.restrictUnitIso
        (Proj.awayι 𝓑 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide)))

end LinearStudy
