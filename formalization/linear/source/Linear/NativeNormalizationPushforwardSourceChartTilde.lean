module
public import Linear.NativeNormalizationPushforwardChartModules
public import Linear.NativeSourceSpecChartTilde
public import Linear.TildePushforward
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ)+d))
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar normalizationHomogeneousSourceChartAlgebra

/-- Actual source-dual pushforward on a base Spec chart is the associated
sheaf of the SAME localized source module with scalars restricted. The
normalization chart square and both constituent sheaf isomorphisms are
constructed; global gluing and canonical identification remain separate. -/
def nativeNormalizationPushforwardSourceChartTildeIso
    (a : R) (ha : a ∈ 𝒜 1)
    [(nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsQuasicoherent]
    (hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1
      (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha))) :
    tilde ((ModuleCat.restrictScalars
      (algebraMap (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).obj
      (ModuleCat.of (CommRingCat.of (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))
        (nativeGradedModuleAwayZero 𝓑 𝒟 (algebraMap R S a)))) ≅
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0)).restrict (Proj.awayι 𝒜 a ha (by decide)) := by
  let φ := CommRingCat.ofHom
    (algebraMap (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))
  let N := ModuleCat.of (CommRingCat.of (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))
    (nativeGradedModuleAwayZero 𝓑 𝒟 (algebraMap R S a))
  let e := nativeSourceSpecChartTildeIso 𝓑 𝒟 hD (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hs
  exact tildePushforwardIso φ N ≪≫
    (Scheme.Modules.pushforward (Spec.map φ)).mapIso e ≪≫
    (nativeNormalizationPushforwardChartModuleIso 𝒜 𝓑 a ha
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0)).symm
end LinearStudy
