module
public import Linear.NativeComplementaryMonomialCechNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The original native multiplication input is exactly the degree-l
monomial basis vector of the actual homogeneous polynomial module. -/
theorem coordinatePositiveMonomialPolynomial_eq_basis (l : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    (⟨monomial (projectiveMonomialPositiveWeight l b).natExponent 1,
      (projectiveMonomialPositiveWeight l b).natExponent_monomial_homogeneous l
        (projectiveMonomialPositiveWeight_nonnegative l b) 1⟩ : homogeneousSubmodule σ K l) =
    projectiveHomogeneousMonomialBasis (R := K) l b := by
  apply Subtype.ext
  change monomial (projectiveMonomialPositiveWeight l b).natExponent 1 =
    (projectiveHomogeneousMonomialBasis (R := K) l b).1
  rw [projectiveMonomialPositiveWeight_natExponent, projectiveHomogeneousMonomialBasis_coe]

/-- The previously published native top Cech duality uses exactly the
native/Laurent comparison followed by the actual Laurent residue duality. -/
theorem coordinateNativeGeneralTopHomologyDualIso_eq_comparison (m n : ℕ)
    (hc : Fintype.card σ = n+2) :
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) m n hc).hom =
    HomologicalComplex.homologyMap
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
        (-(m:ℤ)-Fintype.card σ)).hom (n+1) ≫
      (coordinateLaurentFullTopHomologyDualIso (K := K) (σ := σ) m n hc).hom := by
  simp only [coordinateNativeGeneralTopHomologyDualIso, coordinateLaurentFullTopHomologyDualIso,
    Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, Category.assoc]

/-- Let P=Proj K[sigma], T(k) the original locally homogeneous twist,
and b a degree-l monomial. Then its ACTUAL sheaf multiplication induces
the transpose of ACTUAL homogeneous polynomial multiplication on top
Cech homology, under the already verified native top duality.
The only normalization is the proved equality of integer degrees.
This statement does not assert a comparison with derived sheaf cohomology. -/
theorem coordinateNativeGeneralTopHomologyDualIso_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    HomologicalComplex.homologyMap (coordinateNativeComplementaryMonomialComplexMap (K := K) l m b) (n+1) ≫
      (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) m n hc).hom =
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)) := by
  rw [coordinateNativeGeneralTopHomologyDualIso_eq_comparison,
    coordinateNativeGeneralTopHomologyDualIso_eq_comparison]
  have h := coordinateNativeComplementaryMonomialHomology_naturality (K := K) l m (n+1) b
  rw [← Category.assoc, ← h, Category.assoc,
    coordinateLaurentFullTopHomologyDualIso_monomial_naturality, ← Category.assoc]

end MvPolynomial
