module
public import Linear.IntegerFinitePresentationAbelianCoefficientNaturality
public import Linear.CoordinateNativeCechAbelianModel
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
open LinearStudy
/-- The SAME polynomial presentation-data comparison after exact scalar
forgetting,with its original module Cech homology object cached. -/
def coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso
    [Module.Finite (MvPolynomial σ K) M]
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :
    nativeProjectiveOrderedModuleCechHomologyObject (homogeneousSubmodule σ K) D hD
      (homogeneousProjπ (R:=K) (σ:=σ)) (fun i : ULift.{0} σ => X i.down) k (q+1) ≅
      (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K
        (Module.Dual K (integerGradedHomPiece (homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k)))) :=
  (coordinateNativeCechAbelianModelIso q
    (nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD k)).symm ≪≫
  (forget₂ (ModuleCat K) AddCommGrpCat).mapIso
    (coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hD q hcard k)
end MvPolynomial
