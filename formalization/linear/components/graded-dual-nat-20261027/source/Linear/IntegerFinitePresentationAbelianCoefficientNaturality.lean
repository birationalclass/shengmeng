module
public import Linear.CoordinateCechCoefficientForgettingIdentity
public import Linear.IntegerGradedHomDualCoefficientObjects
public import Linear.NativeIntegerTwistedPresentationMapDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
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
attribute [local irreducible] AlgebraicGeometry.Spec homogeneousProjπ
  coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso
/-- The SAME polynomial presentation-data coefficient square after exact
scalar forgetting. This caches the functorial proof,not a desired assumption. -/
def coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_abelian_naturality
    [Module.Finite (MvPolynomial σ K) M] [Module.Finite (MvPolynomial σ K) N]
    (f : M →ₗ[MvPolynomial σ K] N)
    (hf : ∀ d : ℤ,∀ x : M,x ∈ D d → f x ∈ E d)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :=
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let eM := coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hD q hcard k
  let eN := coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso E hE q hcard k
  let aK := (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
    ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K) D E hD hE f hf k))
  let deltaK := ModuleCat.ofHom (LinearStudy.integerGradedHomPrecomposition (homogeneousSubmodule σ K)
    D E f hf (-(Fintype.card σ:ℤ)-k)).dualMap
  let sq : CommSq aK eM.hom eN.hom deltaK :=
    ⟨coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_naturality D E hD hE f hf q hcard k⟩
  (F.map_commSq sq).w
end MvPolynomial
