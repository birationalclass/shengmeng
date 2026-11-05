module
public import Linear.NativeIntegerMixedPresentationTopCokernel
public import Linear.IntegerShiftedFreePresentationDualCokernel
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Linear.NativeShiftedFreePresentationTopCechCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
attribute [local instance] MvPolynomial.gradedAlgebra

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    z d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- The WHOLE ORIGINAL mixed INTEGER-weight presentation has ACTUAL top
ORDERED-CECH homology equal to the K-dual of ORIGINAL homogeneous
Hom_S(M,S)_(-N). Uses the proved actual native presentation cokernel,
actual canonical scalar/cokernel preservation,CONSTRUCTED all-integer
free comparisons and their WHOLE ORIGINAL relation square,and original
Hom kernel/dual cokernel. No presentation comparison is supplied.
This is not derived SHEAF cohomology or normalized dualizing identification. -/
def coordinateNativeIntegerPresentationGradedHomDualIso :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD 0)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerGradedHomPiece (homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)))) := by
  let B := homogeneousSubmodule σ K
  let H := coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let e := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B z) (LinearStudy.integerShiftedFreePiece B w)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B z)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) c hc 0
  let ψ := coordinateNativeIntegerPresentationTopCokernelIso z w D hD c β hc hβ honto hex n hcard
  let κ := cokernel.mapIso _ _
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso z n hcard)
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard)
    (coordinateNativeIntegerFreeRelation_duality z w c hc n hcard)
  exact ((F.mapIso ψ).symm.trans (PreservesCokernel.iso F (H.map e))).trans
    (κ.trans (LinearStudy.integerShiftedFreePresentationDualCokernelHomIso
      c B z w hc D β hβ honto hex (-(Fintype.card σ:ℤ))))

/-- The WHOLE mixed INTEGER-weight comparison preserves ORIGINAL beta.
Its actual coefficient dual is evaluation phi(beta(e_j)),not a chosen
abstract isomorphism or an assumed quotient square. -/
theorem coordinateNativeIntegerPresentationGradedHomDualIso_quotient :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w) D
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w)
          hD β hβ 0)) ≫
      (coordinateNativeIntegerPresentationGradedHomDualIso z w D hD c β hc hβ honto hex n hcard).hom =
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreePresentationHomCoefficientMap c
        (homogeneousSubmodule σ K) z w hc D β hβ honto hex (-(Fintype.card σ:ℤ))).dualMap := by
  let B := homogeneousSubmodule σ K
  let H := coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let e := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B z) (LinearStudy.integerShiftedFreePiece B w)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B z)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) c hc 0
  let b := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B w) D
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) hD β hβ 0
  let δ := ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c B z w hc
    (-(Fintype.card σ:ℤ))).dualMap
  let ψ := coordinateNativeIntegerPresentationTopCokernelIso z w D hD c β hc hβ honto hex n hcard
  let κ := cokernel.mapIso _ _
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso z n hcard)
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard)
    (coordinateNativeIntegerFreeRelation_duality z w c hc n hcard)
  let η := LinearStudy.integerShiftedFreePresentationDualCokernelHomIso
    c B z w hc D β hβ honto hex (-(Fintype.card σ:ℤ))
  have hp0 := coordinateNativeIntegerPresentationTopCokernelIso_quotient
    z w D hD c β hc hβ honto hex n hcard
  change cokernel.π (H.map e) ≫ ψ.hom = H.map b at hp0
  have hp : H.map b ≫ ψ.inv = cokernel.π (H.map e) := by
    rw [← hp0,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hk : cokernel.π (F.map (H.map e)) ≫ κ.hom =
      (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard).hom ≫ cokernel.π δ := by
    dsimp only [κ]
    erw [cokernel.mapIso_hom]
    simp only [cokernel.map]
    erw [cokernel.π_desc]
  unfold coordinateNativeIntegerPresentationGradedHomDualIso
  simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv]
  change F.map (H.map b) ≫ F.map ψ.inv ≫
    (PreservesCokernel.iso F (H.map e)).hom ≫ κ.hom ≫ η.hom =
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard).hom ≫ _
  rw [← Category.assoc,← F.map_comp,hp]
  erw [← Category.assoc,PreservesCokernel.π_iso_hom]
  erw [← Category.assoc,hk]
  simp only [Category.assoc]
  exact congrArg (fun t => (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard).hom ≫ t)
    (LinearStudy.integerShiftedFreePresentationDualCokernelHomIso_quotient
      c B z w hc D β hβ honto hex (-(Fintype.card σ:ℤ)))

end MvPolynomial
