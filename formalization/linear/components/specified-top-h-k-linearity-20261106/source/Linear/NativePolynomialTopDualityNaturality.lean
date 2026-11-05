module
public import Linear.NativeScaledMonomialTopDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat
universe u v
variable {B : Type u} [CommRing B] {M N : Type v}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

theorem ofHom_finset_sum {ι : Type*} (s : Finset ι) (f : ι → M →ₗ[B] N) :
    ofHom (∑ i ∈ s, f i) = ∑ i ∈ s, ofHom (f i) := by
  apply ModuleCat.hom_ext
  rw [hom_sum]
  rfl

end ModuleCat

namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- Let P=Proj K[sigma], r=card(sigma)-1>=1 and p any actual degree-l
homogeneous polynomial. Then its ORIGINAL sheaf multiplication induces
the transpose of actual multiplication by the canonically mapped polynomial
on native top Cech homology. The coefficient map and integer degree
normalization are explicit. Derived sheaf cohomology remains separate. -/
theorem coordinateNativeGeneralTopHomologyDualIso_polynomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (p : homogeneousSubmodule σ K l) :
    HomologicalComplex.homologyMap
      (coordinateNativeComplementaryPolynomialComplexMap (K := K) l m p) (n+1) ≫
      (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) m n hc).hom =
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (projectiveHomogeneousCoefficientMap
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom l p)) := by
  classical
  letI : Fintype (ProjectiveMonomialIndex σ l) := Fintype.ofFinite _
  let e := projectiveHomogeneousMonomialBasis (R := K) (σ := σ) l
  let φ := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom
  change coordinateNativeComplementaryPolynomialHomologyAddHom (K := K) l m n p ≫ _ =
    _ ≫ ModuleCat.ofHom (projectiveHomogeneousMultiplyDualFamily l m
      (projectiveHomogeneousCoefficientMap φ l p))
  rw [← e.sum_repr p]
  simp only [map_sum, Preadditive.sum_comp, ModuleCat.ofHom_finset_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [projectiveHomogeneousCoefficientMap_scaled_basis]
  exact coordinateNativeGeneralTopHomologyDualIso_scaled_monomial_naturality l m n hc b (e.repr p b)

end MvPolynomial
