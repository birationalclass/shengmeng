module
public import Linear.NativeDualFullSourceChartEquiv
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- On the ACTUAL affine normalization chart, original degree-zero dual
elements correspond to ALL morphisms from the associated FULL original
source module sheaf to the associated chart-ring module sheaf.
This uses mathlib's actual fully faithful tilde functor. It is not a
comparison with the source Proj canonical sheaf or a finite pushforward. -/
def nativeFullSourceAffineSheafDualEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a ≃
      ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).obj
        (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) ⟶
       (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).obj
        (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝒜 a))) :=
  (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinj).toEquiv.trans
    ((ModuleCat.homEquiv (M := ModuleCat.of (HomogeneousLocalization.Away 𝒜 a) (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) (N := ModuleCat.of (HomogeneousLocalization.Away 𝒜 a) (HomogeneousLocalization.Away 𝒜 a))).symm.trans
      (tilde.fullyFaithfulFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).homEquiv)

/-- The affine sheaf comparison is induced by the already constructed
original full-source-chart functional, not an arbitrary bijection. -/
theorem nativeFullSourceAffineSheafDualEquiv_apply
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeFullSourceAffineSheafDualEquiv 𝒜 𝓑 a ha hinj ell =
      (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).map
        (ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell)) := rfl

/-- Every ACTUAL morphism on the affine normalization chart is obtained
from a unique original native degree-zero dual element. -/
theorem nativeFullSourceAffineSheafDual_existsUnique
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (f : (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).obj
        (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) ⟶
       (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).obj
        (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝒜 a))) :
    ∃! ell, (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).map
      (ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell)) = f := by
  let E := nativeFullSourceAffineSheafDualEquiv 𝒜 𝓑 a ha hinj
  refine ⟨E.symm f,E.apply_symm_apply f,?_⟩
  intro ell hell
  exact E.injective (hell.trans (E.apply_symm_apply f).symm)
end LinearStudy
