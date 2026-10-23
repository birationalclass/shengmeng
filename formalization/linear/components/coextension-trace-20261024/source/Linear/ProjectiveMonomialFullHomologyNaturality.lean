module
public import Linear.ProjectiveMonomialTopHomologyNaturality
public import Linear.ModuleCechScHomologyNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- Independently constructed multiplication on the actual full
Laurent Cech complexes, with the proved integer-degree normalization. -/
def coordinateComplementaryMonomialComplexMap (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) ⟶
    coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ)
      (-(m:ℤ)-Fintype.card σ) where
  f n := ModuleCat.ofHom (coordinateComplementaryMonomialCechShift l m b n)
  comm' n j hj := by
    simp only [ComplexShape.up_Rel] at hj
    subst j
    rw [coordinateNativeLaurentOrderedCechComplex_d, coordinateNativeLaurentOrderedCechComplex_d]
    exact coordinateComplementaryMonomialCechShift_differential l m n b

theorem coordinateComplementaryMonomialComplexMap_sc (l m n : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat (coordinateCanonicalBaseRing K))
      (ComplexShape.up ℕ) n (n+1) (n+2)).map
        (coordinateComplementaryMonomialComplexMap (K := K) l m b) ≫
      (coordinateLaurentGeneralShortComplexIso (K := K) (σ := σ)
        (-(m:ℤ)-Fintype.card σ) n).hom =
    (coordinateLaurentGeneralShortComplexIso (K := K) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n).hom ≫
      coordinateComplementaryMonomialShortComplexMap (K := K) l m n b := by
  apply ShortComplex.Hom.ext
  all_goals simp [coordinateLaurentGeneralShortComplexIso,
    coordinateComplementaryMonomialComplexMap, coordinateComplementaryMonomialShortComplexMap]

/-- The actual full-complex top homology duality, using the previously
proved short-complex comparison and actual residue quotient equivalence. -/
def coordinateLaurentFullTopHomologyDualIso (m n : ℕ)
    (hc : Fintype.card σ = n+2) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ)
      (-(m:ℤ)-Fintype.card σ)).homology (n+1) ≅
    ModuleCat.of (coordinateCanonicalBaseRing K)
      (Module.Dual (coordinateCanonicalBaseRing K)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) m)) :=
  (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ)
      (-(m:ℤ)-Fintype.card σ)).homologyIsoSc' n (n+1) (n+2) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (coordinateLaurentGeneralShortComplexIso _ n) ≪≫
      coordinateLaurentGeneralHomologyDualIso m n hc

/-- On actual full Cech homology, independently constructed monomial
multiplication is transpose to multiplication of actual homogeneous polynomials. -/
theorem coordinateLaurentFullTopHomologyDualIso_monomial_naturality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (b : ProjectiveMonomialIndex σ l) :
    HomologicalComplex.homologyMap (coordinateComplementaryMonomialComplexMap (K := K) l m b) (n+1) ≫
      (coordinateLaurentFullTopHomologyDualIso (K := K) m n hc).hom =
    (coordinateLaurentFullTopHomologyDualIso (K := K) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (projectiveHomogeneousMonomialBasis (R := coordinateCanonicalBaseRing K) l b)) := by
  have h₁ := HomologicalComplex.moduleCatHomologyIsoSc'_naturality
    (coordinateComplementaryMonomialComplexMap (K := K) l m b) n (n+1) (n+2) (by simp) (by simp)
  have h₂ := congrArg (fun f => ShortComplex.homologyMap f)
    (coordinateComplementaryMonomialComplexMap_sc (K := K) l m n b)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h₂
  have h₃ := coordinateLaurentGeneralHomologyDualIso_monomial_naturality (K := K) l m n hc b
  simp only [coordinateLaurentFullTopHomologyDualIso, Iso.trans_hom,
    ShortComplex.homologyMapIso_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

end MvPolynomial
