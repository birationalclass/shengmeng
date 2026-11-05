module
public import Linear.NativePolynomialMultiplicationAdditivity
public import Linear.NativeCechComplexDegreeTransport
public import Linear.ProjectiveHomogeneousCoefficientTransport
public import Linear.NativeScaledMonomialCechNaturality
public import Linear.ProjectiveComplementaryCechShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

def coordinateNativeComplementaryPolynomialComplexMap (l m : ℕ)
    (p : homogeneousSubmodule σ K l) :
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (-((l+m:ℕ):ℤ)-Fintype.card σ))
        (coordinateOpenCover (R := K) (σ := σ)) ⟶
    Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m:ℤ)-Fintype.card σ))
        (coordinateOpenCover (R := K) (σ := σ)) :=
  (Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
    (coordinateOpenCover (R := K) (σ := σ))).map
      (coordinateNativePolynomialMultiplication (K := K) l p (-((l+m:ℕ):ℤ)-Fintype.card σ)) ≫
    coordinateNativeComplexDegreeCast (K := K) (σ := σ) (projectiveComplementaryShiftDegree (σ := σ) l m)

def coordinateNativeComplementaryPolynomialComplexAddHom (l m : ℕ) :
    homogeneousSubmodule σ K l →+
      (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-((l+m:ℕ):ℤ)-Fintype.card σ))
          (coordinateOpenCover (R := K) (σ := σ)) ⟶
       Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m:ℤ)-Fintype.card σ))
          (coordinateOpenCover (R := K) (σ := σ))) where
  toFun p := coordinateNativeComplementaryPolynomialComplexMap l m p
  map_zero' := by
    unfold coordinateNativeComplementaryPolynomialComplexMap
    rw [coordinateNativePolynomialMultiplication_zero, Functor.map_zero, zero_comp]
  map_add' p q := by
    unfold coordinateNativeComplementaryPolynomialComplexMap
    rw [coordinateNativePolynomialMultiplication_add, Functor.map_add, Preadditive.add_comp]

def coordinateNativeComplementaryPolynomialHomologyAddHom (l m n : ℕ) :
    homogeneousSubmodule σ K l →+
      ((Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-((l+m:ℕ):ℤ)-Fintype.card σ))
          (coordinateOpenCover (R := K) (σ := σ))).homology (n+1) ⟶
       (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m:ℤ)-Fintype.card σ))
          (coordinateOpenCover (R := K) (σ := σ))).homology (n+1)) :=
  ((HomologicalComplex.homologyFunctor
      (ModuleCat Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens)))
      (ComplexShape.up ℕ) (n+1)).mapAddHom).comp
    (coordinateNativeComplementaryPolynomialComplexAddHom l m)

theorem coordinateNativeComplementaryPolynomialHomologyAddHom_apply (l m n : ℕ)
    (p : homogeneousSubmodule σ K l) :
    coordinateNativeComplementaryPolynomialHomologyAddHom l m n p =
      HomologicalComplex.homologyMap (coordinateNativeComplementaryPolynomialComplexMap l m p) (n+1) := rfl

theorem coordinatePositiveScaledMonomialPolynomial_eq_basis (l : ℕ)
    (b : ProjectiveMonomialIndex σ l) (κ : K) :
    (⟨monomial (projectiveMonomialPositiveWeight l b).natExponent κ,
      (projectiveMonomialPositiveWeight l b).natExponent_monomial_homogeneous l
        (projectiveMonomialPositiveWeight_nonnegative l b) κ⟩ : homogeneousSubmodule σ K l) =
    κ • projectiveHomogeneousMonomialBasis (R := K) l b := by
  apply Subtype.ext
  change monomial (projectiveMonomialPositiveWeight l b).natExponent κ =
    (κ • projectiveHomogeneousMonomialBasis (R := K) l b).1
  rw [projectiveHomogeneousMonomialBasis_scaled_coe, projectiveMonomialPositiveWeight_natExponent]

end MvPolynomial
