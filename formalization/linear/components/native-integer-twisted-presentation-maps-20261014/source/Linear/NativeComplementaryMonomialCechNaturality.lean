module
public import Linear.ProjectiveMonomialFullHomologyNaturality
public import Linear.NativeCechComplexDegreeTransport
public import Linear.NativeMonomialCechNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem coordinateComplementaryMonomialComplexMap_eq_shift (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    coordinateComplementaryMonomialComplexMap (K := K) l m b =
    coordinateLaurentShiftComplex (K := K) (d := -((l+m:ℕ):ℤ)-Fintype.card σ)
      (projectiveMonomialPositiveWeight l b) (projectiveMonomialPositiveWeight_nonnegative l b) ≫
      coordinateLaurentComplexDegreeCast (K := K) (projectiveComplementaryShiftDegree (σ := σ) l m) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, coordinateLaurentComplexDegreeCast_f]
  rfl

/-- Apply the actual Cech functor to original sheaf multiplication
by X^b, then normalize only the proved equality of integer twist degrees. -/
def coordinateNativeComplementaryMonomialComplexMap (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (-((l+m:ℕ):ℤ)-Fintype.card σ))
        (coordinateOpenCover (R := K) (σ := σ)) ⟶
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m:ℤ)-Fintype.card σ))
        (coordinateOpenCover (R := K) (σ := σ)) :=
  (Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
    (coordinateOpenCover (R := K) (σ := σ))).map
      (coordinateNativePolynomialMultiplication (K := K) l
        ⟨monomial (projectiveMonomialPositiveWeight l b).natExponent 1,
          (projectiveMonomialPositiveWeight l b).natExponent_monomial_homogeneous l
            (projectiveMonomialPositiveWeight_nonnegative l b) 1⟩
        (-((l+m:ℕ):ℤ)-Fintype.card σ)) ≫
    coordinateNativeComplexDegreeCast (K := K) (σ := σ) (projectiveComplementaryShiftDegree (σ := σ) l m)

/-- The normalized native multiplication intertwines with independently
constructed Laurent multiplication on the actual full Cech complexes. -/
theorem coordinateNativeComplementaryMonomialComplex_naturality (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ)).hom ≫
        coordinateComplementaryMonomialComplexMap (K := K) l m b =
    coordinateNativeComplementaryMonomialComplexMap (K := K) l m b ≫
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
        (-(m:ℤ)-Fintype.card σ)).hom := by
  rw [coordinateComplementaryMonomialComplexMap_eq_shift]
  unfold coordinateNativeComplementaryMonomialComplexMap
  have h := coordinateNativeMonomialCechComplex_naturality (K := K) l
    (projectiveMonomialPositiveWeight l b) (projectiveMonomialPositiveWeight_nonnegative l b)
    (-((l+m:ℕ):ℤ)-Fintype.card σ)
  rw [reassoc_of% h, coordinateNativeLaurentComplexDegreeCast_naturality] <;>
    simp only [Category.assoc]

/-- The same native/Laurent multiplication square holds on actual
homology in every degree, by the original mathlib homology functor. -/
theorem coordinateNativeComplementaryMonomialHomology_naturality (l m n : ℕ)
    (b : ProjectiveMonomialIndex σ l) :
    HomologicalComplex.homologyMap
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
        (-((l+m:ℕ):ℤ)-Fintype.card σ)).hom n ≫
      HomologicalComplex.homologyMap (coordinateComplementaryMonomialComplexMap (K := K) l m b) n =
    HomologicalComplex.homologyMap (coordinateNativeComplementaryMonomialComplexMap (K := K) l m b) n ≫
      HomologicalComplex.homologyMap
        (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ)
          (-(m:ℤ)-Fintype.card σ)).hom n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    coordinateNativeComplementaryMonomialComplex_naturality]

end MvPolynomial
