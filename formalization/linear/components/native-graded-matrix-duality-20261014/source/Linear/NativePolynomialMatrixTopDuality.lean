module
public import Linear.NativeGradedPolynomialEntry
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

/-- An ACTUAL original scheme-module matrix between finite sums of
possibly different negative twists. Its entries are homogeneous polynomial
multiplication, and are zero for negative multiplying degrees. -/
def coordinateNativeGradedPolynomialMatrix {I J : Type} [Finite I] [Finite J]
    (a : I → ℕ) (b : J → ℕ)
    (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    (⨁ fun i => coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a i:ℤ)-Fintype.card σ)) ⟶
    (⨁ fun j => coordinateNativeIntegerTwist (K := K) (σ := σ) (-(b j:ℤ)-Fintype.card σ)) :=
  biproduct.matrix (fun i j => coordinateNativeGradedPolynomialEntry (a i) (b j) (p i j))

/-- Matrix of ACTUAL homogeneous multiplication transposes, after the
canonical K-to-global-base-ring coefficient map. No cohomology map is
defined by transporting a matrix through duality. -/
def coordinateCanonicalGradedPolynomialDualMatrix {I J : Type} [Finite I] [Finite J]
    (a : I → ℕ) (b : J → ℕ)
    (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    (⨁ fun i => ModuleCat.of (coordinateCanonicalBaseRing K)
      (Module.Dual (coordinateCanonicalBaseRing K)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) (a i)))) ⟶
    (⨁ fun j => ModuleCat.of (coordinateCanonicalBaseRing K)
      (Module.Dual (coordinateCanonicalBaseRing K)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) (b j)))) :=
  biproduct.matrix (fun i j => projectiveHomogeneousGradedPolynomialDualEntry (a i) (b j)
    (projectiveHomogeneousCoefficientMap
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom
        (a i-b j) (p i j)))

/-- Let I,J be finite, a_i,b_j>=0 arbitrary, card(sigma)=n+2, and p_ij
homogeneous of degree a_i-b_j when nonnegative. Then the ORIGINAL sheaf
matrix induces the actual transposed homogeneous multiplication matrix
under the finite native top-Cech duality isomorphisms. This is the varied
free-twist matrix case; finite-presentation and derived duality remain separate. -/
theorem coordinateNativeGradedPolynomialMatrix_top_duality {I J : Type} [Finite I] [Finite J]
    (a : I → ℕ) (b : J → ℕ) (n : ℕ) (hc : Fintype.card σ = n+2)
    (p : ∀ i j, homogeneousSubmodule σ K (a i-b j)) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeGradedPolynomialMatrix a b p) ≫
      (coordinateNativeFiniteTwistTopHomologyDualIso (K := K) (σ := σ) b n hc).hom =
    (coordinateNativeFiniteTwistTopHomologyDualIso (K := K) (σ := σ) a n hc).hom ≫
      coordinateCanonicalGradedPolynomialDualMatrix a b p := by
  unfold coordinateNativeFiniteTwistTopHomologyDualIso
  simp only [Iso.trans_hom, biproduct.mapIso_hom]
  unfold coordinateNativeGradedPolynomialMatrix coordinateCanonicalGradedPolynomialDualMatrix
  erw [← Category.assoc, coordinateNativeCechHomologyFunctor_matrix]
  simp only [Category.assoc]
  congr 1
  exact LinearStudy.biproductMatrixComponentNaturality
    (fun i j => (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeGradedPolynomialEntry (a i) (b j) (p i j)))
    (fun i j => projectiveHomogeneousGradedPolynomialDualEntry (a i) (b j)
      (projectiveHomogeneousCoefficientMap
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom
          (a i-b j) (p i j)))
    (fun i => (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (a i) n hc).hom)
    (fun j => (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (b j) n hc).hom)
    (fun i j => coordinateNativeGradedPolynomialEntry_top_duality (a i) (b j) n hc (p i j))

end MvPolynomial
