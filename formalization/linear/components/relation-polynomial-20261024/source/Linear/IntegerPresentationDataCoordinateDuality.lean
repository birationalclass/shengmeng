-- Choose valid finite homogeneous presentation data before constructing duality.
-- Choose verified presentation DATA,then construct this specified Cech duality.
module
public import Linear.IntegerGradedFinitePresentationData
public import Linear.NativeIntegerTwistedPresentationCechHomDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ,∀ d : ℤ,∀ p : MvPolynomial σ K,p ∈ homogeneousSubmodule σ K t →
  ∀ x : M,x ∈ D d → p • x ∈ D ((t:ℤ)+d))
/-- Construct specified original Cech/Hom duality from PRESENTATION DATA.
No arbitrary whole-Iso choice. Naturality and presentation independence
are proved in the corresponding separate modules. -/
def coordinateNativeIntegerPresentationDataGradedHomDualIso
    (P : LinearStudy.IntegerGradedFinitePresentationData (homogeneousSubmodule σ K) D)
    (n : ℕ) (hcard : Fintype.card σ=n+2) (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD k)) ≅
      ModuleCat.of K (Module.Dual K (LinearStudy.integerGradedHomPiece
        (homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k))) := by
  classical
  let beta := LinearStudy.integerShiftedFreeGeneratorMap (S:=MvPolynomial σ K)
    (fun i : P.generators => (i : M))
  let rel := LinearStudy.integerShiftedFreeGeneratorMap (S:=MvPolynomial σ K)
    (fun i : P.relations => ((i : beta.ker) : P.generators → MvPolynomial σ K))
  exact coordinateNativeIntegerTwistedPresentationGradedHomDualIso
    P.relationDegrees P.generatorDegrees D hD rel beta P.relation_homogeneous
    P.generator_homogeneous P.generator_surjective P.relation_exact n hcard k
/-- Actual finite-module data selects verified presentation data first.
Independence and naturality are proved separately. -/
def coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso
    [Module.Finite (MvPolynomial σ K) M]
    (n : ℕ) (hcard : Fintype.card σ=n+2) (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD k)) ≅
      ModuleCat.of K (Module.Dual K (LinearStudy.integerGradedHomPiece
        (homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)-k))) :=
  coordinateNativeIntegerPresentationDataGradedHomDualIso D hD
    (LinearStudy.integerGradedFiniteChosenPresentationData (homogeneousSubmodule σ K) D hD) n hcard k
end MvPolynomial
