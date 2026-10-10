module
public import Linear.NativeFullSourceAffineSheafDual
public import Linear.TildePushforward
public import Linear.ExtendScalarsActualTensor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The actual normalization chart algebra gives the actual affine
pushforward of the source structure sheaf. No pushforward certificate
is supplied as an input. -/
def nativeNormalizationChartStructurePushforwardIso (a : R) :
    tilde (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) ≅
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
      (algebraMap (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).ringCatSheaf) := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap A B)
  let e : ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of B B)) ≅
      ModuleCat.of A B := (restrictedAlgebraModuleEquiv (R := A) (S := B)).toModuleIso
  exact (tilde.functor (CommRingCat.of A)).mapIso e.symm ≪≫
    tildePushforwardIso φ (ModuleCat.of B B) ≪≫
    (Scheme.Modules.pushforward (Spec.map φ)).mapIso tildeSelf

/-- On the actual affine normalization chart, every structure-sheaf
functional on the actual affine pushforward comes from exactly one
original native degree-zero normalization-dual element. This is the
finite-chart duality comparison; canonical-sheaf identification and
gluing on the original projective map remain separate obligations. -/
def nativeFullSourceAffinePushforwardDualEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a ≃
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).ringCatSheaf) ⟶
       SheafOfModules.unit (Spec (CommRingCat.of
          (HomogeneousLocalization.Away 𝒜 a))).ringCatSheaf) := by
  let e := nativeNormalizationChartStructurePushforwardIso 𝒜 𝓑 a
  let t : tilde (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝒜 a)) ≅
      SheafOfModules.unit (Spec (CommRingCat.of
        (HomogeneousLocalization.Away 𝒜 a))).ringCatSheaf := tildeSelf
  exact (nativeFullSourceAffineSheafDualEquiv 𝒜 𝓑 a ha hinj).trans {
    toFun f := e.inv ≫ f ≫ t.hom
    invFun f := e.hom ≫ f ≫ t.inv
    left_inv f := by simp [Category.assoc]
    right_inv f := by simp [Category.assoc] }

end LinearStudy
