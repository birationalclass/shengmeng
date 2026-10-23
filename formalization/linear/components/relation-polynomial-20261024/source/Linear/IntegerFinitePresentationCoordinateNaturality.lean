module
public import Linear.IntegerPresentationDataCoordinateIndependence
public import Linear.NativeIntegerTwistedPresentationMapDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M N : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
variable [AddCommGroup N] [Module K N] [Module (MvPolynomial σ K) N]
variable [IsScalarTower K (MvPolynomial σ K) N]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (E : ℤ → Submodule K N) [DirectSum.Decomposition E]
variable (hD : ∀ t : ℕ,∀ d : ℤ,∀ p : MvPolynomial σ K,p ∈ homogeneousSubmodule σ K t →
  ∀ x : M,x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (hE : ∀ t : ℕ,∀ d : ℤ,∀ p : MvPolynomial σ K,p ∈ homogeneousSubmodule σ K t →
  ∀ x : N,x ∈ E d → p • x ∈ E ((t:ℤ)+d))
attribute [local irreducible] coordinateNativeIntegerPresentationDataGradedHomDualIso
  coordinateNativeCechHomologyFunctor LinearStudy.nativeProjectiveModuleSheaf
  LinearStudy.nativeProjectiveDegreeZeroSheafMap
/-- The SAME finite-module-chosen presentation-data comparison is natural
for the ORIGINAL degree-zero map in EVERY integer twist. The two finite
homogeneous presentation data are the previously specified choices;
no whole-isomorphism choice and no desired square are assumed. -/
theorem coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_naturality
    [Module.Finite (MvPolynomial σ K) M] [Module.Finite (MvPolynomial σ K) N]
    (e : M →ₗ[MvPolynomial σ K] N)
    (he : ∀ d : ℤ,∀ x : M,x ∈ D d → e x ∈ E d)
    (n : ℕ) (hcard : Fintype.card σ=n+2) (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          D E hD hE e he k)) ≫
      (coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso E hE n hcard k).hom =
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hD n hcard k).hom ≫
      ModuleCat.ofHom (LinearStudy.integerGradedHomPrecomposition (homogeneousSubmodule σ K)
        D E e he (-(Fintype.card σ:ℤ)-k)).dualMap := by
  simpa only [coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso] using
    coordinateNativeIntegerPresentationDataGradedHomDualIso_naturality D E hD hE
    (LinearStudy.integerGradedFiniteChosenPresentationData (homogeneousSubmodule σ K) D hD)
    (LinearStudy.integerGradedFiniteChosenPresentationData (homogeneousSubmodule σ K) E hE)
    e he n hcard k
end MvPolynomial
