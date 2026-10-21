module
public import Linear.NativeProjectiveMatrixHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- Let I be finite and m_i>=0. The ACTUAL finite biproduct of original
native twists has top Cech homology dual to the corresponding finite
family of ACTUAL homogeneous polynomial pieces, including varied twists.
This is a free-twist case, not coherent presentation/derived duality. -/
def coordinateNativeFiniteTwistTopHomologyDualIso {I : Type} [Finite I]
    (m : I → ℕ) (n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (⨁ fun i => coordinateNativeIntegerTwist (K := K) (σ := σ)
        (-(m i:ℤ)-Fintype.card σ)) ≅
    (⨁ fun i => ModuleCat.of (coordinateCanonicalBaseRing K)
      (Module.Dual (coordinateCanonicalBaseRing K)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) (m i)))) :=
  (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).mapBiproduct
      (fun i => coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m i:ℤ)-Fintype.card σ)) ≪≫
    biproduct.mapIso (fun i => coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (m i) n hc)

end MvPolynomial
