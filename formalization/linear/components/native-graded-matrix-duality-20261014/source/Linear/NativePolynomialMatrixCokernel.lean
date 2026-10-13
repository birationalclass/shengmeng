module
public import Linear.NativePolynomialMatrixTopDuality
public import Mathlib.Algebra.Category.ModuleCat.Abelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The ACTUAL cokernel of the induced native homology matrix is
isomorphic to the actual cokernel of its transposed polynomial matrix.
This is NOT an identification with homology of the sheaf cokernel;
that affine exactness/top-Cech presentation bridge remains to prove. -/
def coordinateNativePolynomialMatrixCokernelDualIso {I J : Type} [Finite I] [Finite J]
    (a : I → ℕ) (b : J → ℕ) (n : ℕ) (hc : Fintype.card σ = n+2)
    (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    cokernel ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeGradedPolynomialMatrix a b p)) ≅
    cokernel (coordinateCanonicalGradedPolynomialDualMatrix a b p) :=
  cokernel.mapIso _ _
    (coordinateNativeFiniteTwistTopHomologyDualIso (K := K) (σ := σ) a n hc)
    (coordinateNativeFiniteTwistTopHomologyDualIso (K := K) (σ := σ) b n hc)
    (coordinateNativeGradedPolynomialMatrix_top_duality a b n hc p)

/-- The cokernel comparison is compatible with the actual quotient maps,
rather than an arbitrary isomorphism of abstract modules. -/
theorem coordinateNativePolynomialMatrixCokernelDualIso_quotient {I J : Type} [Finite I] [Finite J]
    (a : I → ℕ) (b : J → ℕ) (n : ℕ) (hc : Fintype.card σ = n+2)
    (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    cokernel.π ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeGradedPolynomialMatrix a b p)) ≫
      (coordinateNativePolynomialMatrixCokernelDualIso a b n hc p).hom =
    (coordinateNativeFiniteTwistTopHomologyDualIso (K := K) (σ := σ) b n hc).hom ≫
      cokernel.π (coordinateCanonicalGradedPolynomialDualMatrix a b p) := by
  simp [coordinateNativePolynomialMatrixCokernelDualIso, cokernel.map]

end MvPolynomial
