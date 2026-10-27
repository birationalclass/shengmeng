module
public import Linear.IntegerFinitePresentationAbelianCoefficientNaturality
public import Linear.IntegerFinitePresentationAbelianComparisonFactorization
public import Linear.CoordinateNativeCechAbelianModelCoefficient
public import Linear.CategoricalComparisonCoefficientFactorization
public import Linear.NativeProjectiveModuleCechHomologyObjects
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
  LinearStudy.nativeProjectiveModuleSheaf
  LinearStudy.nativeProjectiveDegreeZeroSheafMap
attribute [local irreducible] coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso
  coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso
open LinearStudy
/-- Original coefficient naturality of that SAME comparison; the native
module Cech map and actual dual precomposition values are retained. -/
def coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso_coefficient_proof
    [Module.Finite (MvPolynomial σ K) M] [Module.Finite (MvPolynomial σ K) N]
    (f : M →ₗ[MvPolynomial σ K] N) (hf : ∀ d : ℤ,∀ x : M,x ∈ D d → f x ∈ E d)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :=

  let g := nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K) D E hD hE f hf k
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let C := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let aF := F.map (C.map ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) q).map g))
  originalComparisonIsoCoefficientSquare_of_factorizations
    (coordinateNativeCechAbelianModelIso q (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD k)).symm
    (coordinateNativeCechAbelianModelIso q (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) E hE k)).symm
    (F.mapIso (coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hD q hcard k))
    (F.mapIso (coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso E hE q hcard k))
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso D hD q hcard k)
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso E hE q hcard k)
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso_factorization D hD q hcard k)
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso_factorization E hE q hcard k)
    (nativeProjectiveOrderedModuleCechHomologyCoefficientHom (homogeneousSubmodule σ K) D E hD hE
      (homogeneousProjπ (R:=K) (σ:=σ)) f hf (fun i : ULift.{0} σ => X i.down) k (q+1))
    aF (integerGradedHomDualCoefficientHom (homogeneousSubmodule σ K) D E f hf (-(Fintype.card σ:ℤ)-k))
    (coordinateNativeCechAbelianModelIso_coefficient g q).w
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_abelian_naturality D E hD hE f hf q hcard k)
end MvPolynomial
