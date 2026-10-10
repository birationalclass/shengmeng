module
public import Linear.NativeNormalizationProjectiveMap
public import Linear.SchemeModuleChartPushforwardRestriction
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

/-- On the SAME original normalization chart, the actual GLOBAL
pushforward module restricted to Spec A_i is the actual AFFINE
pushforward of the same original source module restricted to Spec B_i.
The chart square is proved from the original graded normalization. -/
def nativeNormalizationPushforwardChartModuleIso
    (a : R) (ha : a ∈ 𝒜 1) (M : (Proj 𝓑).Modules) :
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M).restrict
      (Proj.awayι 𝒜 a ha (by decide)) ≅
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
      (M.restrict (Proj.awayι 𝓑 (algebraMap R S a)
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide))) := by
  exact schemeModuleChartPushforwardRestrictionIso
    (nativeNormalizationProjectiveMap 𝒜 𝓑) (Proj.basicOpen 𝒜 a)
    (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide))
    (Proj.basicOpenIsoSpec 𝒜 a ha (by decide)) _
    (nativeNormalizationProjectiveMap_chart_restriction 𝒜 𝓑 a ha) M

end LinearStudy
