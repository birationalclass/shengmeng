module
public import Linear.NativeAffineDualScalar
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

/-- Addition of the ORIGINAL degree-zero dual elements is carried to
addition of their actual affine pushforward functionals. -/
theorem nativeFullSourceAffinePushforwardDualEquiv_add
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell k : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (ell + k) =
      nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell +
        nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj k := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let e := nativeNormalizationChartStructurePushforwardIso 𝒜 𝓑 a
  let t : tilde (ModuleCat.of A A) ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf := tildeSelf
  let F := tilde.functor (CommRingCat.of A)
  change e.inv ≫ F.map (ModuleCat.ofHom
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj (ell + k))) ≫ t.hom =
    (e.inv ≫ F.map (ModuleCat.ofHom
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell)) ≫ t.hom) +
    (e.inv ≫ F.map (ModuleCat.ofHom
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj k)) ≫ t.hom)
  rw [map_add]
  change e.inv ≫ F.map (ModuleCat.ofHom
      (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell) +
        ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj k)) ≫ t.hom = _
  have hf := tilde.map_add (R := CommRingCat.of A)
    (ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell))
    (ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj k))
  refine (congrArg (fun h => e.inv ≫ h ≫ t.hom) hf).trans ?_
  apply SheafOfModules.hom_ext
  ext U x
  change (t.hom.app U.unop).hom
      (((F.map (ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell))).app
        U.unop).hom ((e.inv.app U.unop).hom x) +
       ((F.map (ModuleCat.ofHom (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj k))).app
        U.unop).hom ((e.inv.app U.unop).hom x)) = _
  exact (t.hom.app U.unop).hom.map_add _ _

end LinearStudy
