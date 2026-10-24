module
public import Linear.IntegerPresentationDataCoordinateDuality
public import Linear.NativeIntegerTwistedPresentationMapDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
/-- The specified comparison from ANY TWO valid presentation data is
natural for the ACTUAL degree-zero map and EVERY original integer twist.
The required homogeneous lift is constructed by the existing map theorem. -/
theorem coordinateNativeIntegerPresentationDataGradedHomDualIso_naturality
    (P : LinearStudy.IntegerGradedFinitePresentationData (homogeneousSubmodule σ K) D)
    (Q : LinearStudy.IntegerGradedFinitePresentationData (homogeneousSubmodule σ K) E)
    (e : M →ₗ[MvPolynomial σ K] N)
    (he : ∀ d : ℤ,∀ x : M,x ∈ D d → e x ∈ E d)
    (n : ℕ) (hcard : Fintype.card σ=n+2) (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          D E hD hE e he k)) ≫
      (coordinateNativeIntegerPresentationDataGradedHomDualIso E hE Q n hcard k).hom =
    (coordinateNativeIntegerPresentationDataGradedHomDualIso D hD P n hcard k).hom ≫
      ModuleCat.ofHom (LinearStudy.integerGradedHomPrecomposition (homogeneousSubmodule σ K)
        D E e he (-(Fintype.card σ:ℤ)-k)).dualMap := by
  classical
  exact coordinateNativeIntegerTwistedPresentationMap_duality
    P.relationDegrees P.generatorDegrees Q.relationDegrees Q.generatorDegrees
    D E hD hE _ _ _ _ P.relation_homogeneous P.generator_homogeneous
    Q.relation_homogeneous Q.generator_homogeneous P.generator_surjective P.relation_exact
    Q.generator_surjective Q.relation_exact e he n hcard k
end MvPolynomial
