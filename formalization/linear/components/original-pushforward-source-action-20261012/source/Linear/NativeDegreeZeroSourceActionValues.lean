module
public import Linear.NativeDegreeZeroSourceInverseValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
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

/-- The ORIGINAL native source-chart action, pulled back through the
SAME original degree-zero comparison, has its original full-localization
value. The abstract localization action is proved equal to the native one. -/
theorem nativeCoextensionBaseSourceZeroChartEquiv_symm_source_smul_val
    (a : R) (ha : a ∈ 𝒜 1)
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    letI : Module (Localization.Away (algebraMap R S a))
      (LocalizedModule (Submonoid.powers (algebraMap R S a)) D) :=
        nativeLocalizedModuleScalar (Submonoid.powers (algebraMap R S a))
    ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm
        (b • nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell)).val =
      (moduleBaseSourceLocalizationEquiv (S := S) a).symm
        (b.val • moduleBaseSourceLocalizationEquiv (S := S) a ell.val) := by
  dsimp only
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  letI : Module (Localization.Away (algebraMap R S a))
    (LocalizedModule (Submonoid.powers (algebraMap R S a)) D) :=
      nativeLocalizedModuleScalar (Submonoid.powers (algebraMap R S a))
  rw [nativeCoextensionBaseSourceZeroChartEquiv_symm_val]
  apply congrArg (moduleBaseSourceLocalizationEquiv (S := S) a).symm
  calc
    (b • nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell).val =
      b.val • (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell).val :=
      by rfl
    _ = b.val • moduleBaseSourceLocalizationEquiv (S := S) a ell.val := by
      rw [nativeCoextensionBaseSourceZeroChartEquiv_apply]

end LinearStudy
