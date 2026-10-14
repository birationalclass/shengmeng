module
public import Linear.NativeOriginalPresentationCanonicalScalarCokernel
public import Linear.NativeOriginalPolynomialCokernelHomDual
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The ACTUAL original weighted-free top Cech comparison with its
ORIGINAL degree -N Hom coefficient dual,using original affine scalars,
original finite dual assembly and proved original polynomial coordinates. -/
def coordinateNativeOriginalFreeCoefficientDualIso {L : Type}
    [Fintype L] [DecidableEq L] (a : L → ℕ) (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
            (fun i => coordinatePresentationWeight (σ := σ) (a i)))
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
            (fun i => coordinatePresentationWeight (σ := σ) (a i))) 0)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerShiftedFreeDualCoordinatePiece (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i)) (-(Fintype.card σ:ℤ)))) :=
  ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).mapIso
    (coordinateNativeOriginalFreeTopHomologyDualIso a n hcard)).trans
      ((coordinateCanonicalFiniteHomogeneousDualCoefficientIso K a).symm.trans
        (coordinateOriginalDegreeCoefficientDualIso a))

variable {M : Type} [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (a : I → ℕ) (b : J → ℕ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- The ACTUAL original positive-weight finite-presentation prefixes are
now UNIFIED:original top ORDERED-CECH homology of native M(0),under
original canonical scalar restriction,is the K-dual of ORIGINAL
Hom_S(M,S)_(-N),N=card(sigma). All original presentation,entry,coordinate,
scalar and cokernel comparisons are constructed,not supplied premises.
This is not yet derived sheaf cohomology or normalized dualizing theory. -/
def coordinateNativeOriginalPresentationGradedHomDualIso :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD 0)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerGradedHomPiece (homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)))) :=
  (coordinateNativeOriginalPresentationKPolynomialTopCokernelIso
    a b D hD c β hc hβ honto hex n hcard).trans
      (coordinateOriginalPresentationPolynomialDualHomIso a b D c β hc hβ honto hex)

/-- The unified ACTUAL original Cech/Hom duality respects ORIGINAL beta.
The final dual map evaluates on original coefficients phi(beta(e_j)).
This proves the actual original quotient square,not only an abstract iso. -/
theorem coordinateNativeOriginalPresentationGradedHomDualIso_quotient :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
            (fun j => coordinatePresentationWeight (σ := σ) (b j))) D
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
            (fun j => coordinatePresentationWeight (σ := σ) (b j))) hD β hβ 0)) ≫
      (coordinateNativeOriginalPresentationGradedHomDualIso
        a b D hD c β hc hβ honto hex n hcard).hom =
    (coordinateNativeOriginalFreeCoefficientDualIso b n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreePresentationHomCoefficientMap c
        (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc
        D β hβ honto hex (-(Fintype.card σ:ℤ))).dualMap := by
  unfold coordinateNativeOriginalPresentationGradedHomDualIso
  simp only [Iso.trans_hom]
  erw [← Category.assoc,coordinateNativeOriginalPresentationKPolynomialTopCokernelIso_quotient]
  simp only [Category.assoc]
  erw [coordinateOriginalPresentationPolynomialDualHomIso_quotient]
  simp [coordinateNativeOriginalFreeCoefficientDualIso]

end MvPolynomial
