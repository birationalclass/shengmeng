module
public import Linear.NativeFiniteTwistTopDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- Genuine equality transport between the ORIGINAL integer-twist sheaves. -/
def coordinateNativeSheafDegreeCast {d d' : ℤ} (h : d = d') :
    coordinateNativeIntegerTwist (K := K) (σ := σ) d ⟶
      coordinateNativeIntegerTwist (K := K) (σ := σ) d' :=
  eqToHom (congrArg (fun q => coordinateNativeIntegerTwist (K := K) (σ := σ) q) h)

/-- The original Cech functor takes sheaf equality transport to the already
constructed complex equality transport. -/
theorem coordinateNativeSheafDegreeCast_cech {d d' : ℤ} (h : d = d') :
    (Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ))).map
      (coordinateNativeSheafDegreeCast (K := K) (σ := σ) h) =
    coordinateNativeComplexDegreeCast (K := K) (σ := σ) h := by
  cases h
  simp [coordinateNativeSheafDegreeCast, coordinateNativeComplexDegreeCast]

/-- ORIGINAL polynomial sheaf multiplication, with its target degree
identified by the proved integer equality, before taking Cech homology. -/
def coordinateNativeComplementaryPolynomialSheafMap (l m : ℕ)
    (p : homogeneousSubmodule σ K l) :
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-((l+m:ℕ):ℤ)-Fintype.card σ) ⟶
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-(m:ℤ)-Fintype.card σ) :=
  coordinateNativePolynomialMultiplication l p (-((l+m:ℕ):ℤ)-Fintype.card σ) ≫
    coordinateNativeSheafDegreeCast (projectiveComplementaryShiftDegree (σ := σ) l m)

theorem coordinateNativeComplementaryPolynomialSheafMap_cech (l m : ℕ)
    (p : homogeneousSubmodule σ K l) :
    (Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ))).map
      (coordinateNativeComplementaryPolynomialSheafMap l m p) =
    coordinateNativeComplementaryPolynomialComplexMap (K := K) l m p := by
  unfold coordinateNativeComplementaryPolynomialSheafMap coordinateNativeComplementaryPolynomialComplexMap
  rw [Functor.map_comp, coordinateNativeSheafDegreeCast_cech]

/-- The already proved polynomial transpose square is now a statement about
the ACTUAL homology functor applied to ORIGINAL sheaf multiplication. -/
theorem coordinateNativeComplementaryPolynomialSheafMap_top_duality (l m n : ℕ)
    (hc : Fintype.card σ = n+2) (p : homogeneousSubmodule σ K l) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeComplementaryPolynomialSheafMap l m p) ≫
        (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) m n hc).hom =
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) (l+m) n hc).hom ≫
      ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l m
        (projectiveHomogeneousCoefficientMap
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom l p)) := by
  change HomologicalComplex.homologyMap
    ((Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ))).map
        (coordinateNativeComplementaryPolynomialSheafMap l m p)) (n+1) ≫ _ = _
  rw [coordinateNativeComplementaryPolynomialSheafMap_cech]
  exact coordinateNativeGeneralTopHomologyDualIso_polynomial_naturality l m n hc p

end MvPolynomial
