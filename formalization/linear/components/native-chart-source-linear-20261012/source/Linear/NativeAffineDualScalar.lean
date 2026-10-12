module
public import Linear.NativeFullSourceAffinePushforwardDual
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
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

/-- Scalar multiplication on the ORIGINAL finite dual chart becomes
postcomposition with the ACTUAL multiplication endomorphism of its affine
structure sheaf. The map and its original tilde comparisons are retained. -/
theorem nativeFullSourceAffinePushforwardDualEquiv_smul
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (c : HomogeneousLocalization.Away 𝒜 a)
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let t : tilde (ModuleCat.of A A) ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf := tildeSelf
    nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (c • ell) =
      nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell ≫ t.inv ≫
        (tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (c • (LinearMap.id : A →ₗ[A] A))) ≫ t.hom := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let e := nativeNormalizationChartStructurePushforwardIso 𝒜 𝓑 a
  let t : tilde (ModuleCat.of A A) ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf := tildeSelf
  let F := tilde.functor (CommRingCat.of A)
  have h : ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj (c • ell)) =
      ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell) ≫
        ModuleCat.ofHom (c • (LinearMap.id : A →ₗ[A] A)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj (c • ell)) x =
      c • (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell) x
    rw [map_smul]
    rfl
  dsimp only
  change e.inv ≫ F.map (ModuleCat.ofHom
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj (c • ell))) ≫ t.hom =
    (e.inv ≫ F.map (ModuleCat.ofHom
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell)) ≫ t.hom) ≫ t.inv ≫
      F.map (ModuleCat.ofHom (c • (LinearMap.id : A →ₗ[A] A))) ≫ t.hom
  rw [h, F.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end LinearStudy
