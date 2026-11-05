module
public import Linear.BiproductMatrixNaturality
public import Linear.NativePolynomialTopDualityNaturality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- The ACTUAL original scheme-module Cech functor followed by the
actual homology functor. The native twist is not replaced by coordinates. -/
def coordinateNativeCechHomologyFunctor (n : ℕ) :
    (Proj (homogeneousSubmodule σ K)).Modules ⥤ ModuleCat (coordinateCanonicalBaseRing K) :=
  Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
    (coordinateOpenCover (R := K) (σ := σ)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat (coordinateCanonicalBaseRing K))
      (ComplexShape.up ℕ) (n+1)

instance coordinateNativeCechHomologyFunctor_additive (n : ℕ) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).Additive := by
  unfold coordinateNativeCechHomologyFunctor
  infer_instance

theorem coordinateNativeCechHomologyFunctor_obj (n : ℕ) (k : ℤ) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k) =
    (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ))).homology (n+1) := rfl

/-- An ACTUAL assembled finite matrix of original scheme-module maps
is mapped to its actual homology-entry matrix. Families may have different
twists; no polynomial-presentation duality is claimed by this lemma alone. -/
theorem coordinateNativeCechHomologyFunctor_matrix {I J : Type} [Finite I] [Finite J]
    (n : ℕ) {a : I → (Proj (homogeneousSubmodule σ K)).Modules}
    {b : J → (Proj (homogeneousSubmodule σ K)).Modules}
    (u : ∀ i j, a i ⟶ b j) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map (biproduct.matrix u) ≫
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).mapBiproduct b).hom =
    ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).mapBiproduct a).hom ≫
      biproduct.matrix (fun i j => (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map (u i j)) := by
  exact LinearStudy.additiveFunctorBiproductMatrixNaturality _ u

end MvPolynomial
