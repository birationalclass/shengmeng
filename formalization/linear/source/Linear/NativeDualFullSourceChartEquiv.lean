module
public import Linear.NativeDualFullSourceChartSurjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The original comparison, with both directions proved on the FULL
actual source chart. This remains an algebraic dual comparison, not yet
a canonical-sheaf identification. -/
theorem finiteNativeDualFullSourceChartMap_bijective
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    Function.Bijective (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj) :=
  ⟨finiteNativeDualFullSourceChartMap_injective 𝒜 𝓑 a ha hinj,
    finiteNativeDualFullSourceChartMap_surjective 𝒜 𝓑 a ha hinj⟩

/-- A constructed linear equivalence from the ACTUAL original degree-zero
native coextension chart onto the ACTUAL full original source-chart dual. -/
def finiteNativeDualFullSourceChartEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a
      ≃ₗ[HomogeneousLocalization.Away 𝒜 a]
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
          →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) :=
  LinearEquiv.ofBijective (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj)
    (finiteNativeDualFullSourceChartMap_bijective 𝒜 𝓑 a ha hinj)

theorem finiteNativeDualFullSourceChartEquiv_apply
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinj ell =
      finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell := rfl
end LinearStudy
