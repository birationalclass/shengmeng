module
public import Linear.NativeAffineDualScalar
public import Linear.OriginalTildeScalar
public import Linear.SchemeModuleHomTopScalars
public import Linear.NativeAffineDualAdd
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u

@[instance_reducible] def originalAffineHomBaseModule
    (A : CommRingCat.{u}) (M N : (Spec A).Modules) :
    Module A Γ(schemeModuleHomModuleSheaf M N,⊤) := inferInstance

variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The specified native dual chart comparison takes values in actual
whole-affine sections of the actual internal Hom O-module sheaf. -/
def nativeAffineInternalHomSectionsEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a ≃
      Γ(schemeModuleHomModuleSheaf ((Scheme.Modules.pushforward g).obj
          (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
        (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤) :=
  (nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj).trans
    (schemeModuleHomTopSectionsEquiv _ _).symm

/-- ORIGINAL degree-zero scalars agree with the ACTUAL internal Hom
module scalar action. No scalar-compatibility certificate is supplied. -/
theorem nativeAffineInternalHomSectionsEquiv_smul
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (c : HomogeneousLocalization.Away 𝒜 a)
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let M := (Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let N : (Spec (CommRingCat.of A)).Modules :=
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    letI := originalAffineHomBaseModule (CommRingCat.of A) M N
    nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj (c • ell) =
      c • nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj ell := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let M := (Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let N : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  apply (schemeModuleHomTopSectionsEquiv M N).injective
  change schemeModuleHomTopSectionsEquiv M N
      ((schemeModuleHomTopSectionsEquiv M N).symm
        (nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (c • ell))) = _
  rw [Equiv.apply_symm_apply]
  change nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (c • ell) =
    schemeModuleHomTopSectionsEquiv M N
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c •
        (schemeModuleHomTopSectionsEquiv M N).symm
          (nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell))
  rw [schemeModuleHomTopSectionsEquiv_smul, Equiv.apply_symm_apply]
  change nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (c • ell) =
    nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell ≫
      originalGlobalModuleScalar ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) N
  have hs := nativeFullSourceAffinePushforwardDualEquiv_smul 𝒜 𝓑 a ha hinj c ell
  exact hs.trans (congrArg
    (fun f => nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell ≫ f)
    (originalTildeScalar_unit (R := CommRingCat.of A) c))

/-- Addition agrees with the ACTUAL Hom module section addition. -/
theorem nativeAffineInternalHomSectionsEquiv_add
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell k : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj (ell + k) =
      nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj ell +
        nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj k := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let M := (Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let N : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  apply (schemeModuleHomTopSectionsEquiv M N).injective
  change schemeModuleHomTopSectionsEquiv M N
      ((schemeModuleHomTopSectionsEquiv M N).symm
        (nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (ell + k))) = _
  rw [Equiv.apply_symm_apply, schemeModuleHomTopSectionsEquiv_add]
  change nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj (ell + k) =
    nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj ell +
      nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha hinj k
  exact nativeFullSourceAffinePushforwardDualEquiv_add 𝒜 𝓑 a ha hinj ell k

/-- The SAME specified ORIGINAL finite-dual chart comparison is now an
actual LINEAR equivalence, with the real affine Hom module section action.
This is a chart comparison, not a supplied global finite-duality theorem. -/
def nativeAffineInternalHomSectionsLinearEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let M := (Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let N : (Spec (CommRingCat.of A)).Modules :=
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    letI := originalAffineHomBaseModule (CommRingCat.of A) M N
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a ≃ₗ[A]
      Γ(schemeModuleHomModuleSheaf M N,⊤) := by
  dsimp only
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let M := (Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let N : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  letI : Module A Γ(schemeModuleHomModuleSheaf M N,⊤) :=
    originalAffineHomBaseModule (CommRingCat.of A) M N
  exact {
    __ := nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
    map_add' := nativeAffineInternalHomSectionsEquiv_add 𝒜 𝓑 a ha hinj
    map_smul' := nativeAffineInternalHomSectionsEquiv_smul 𝒜 𝓑 a ha hinj }

end LinearStudy
