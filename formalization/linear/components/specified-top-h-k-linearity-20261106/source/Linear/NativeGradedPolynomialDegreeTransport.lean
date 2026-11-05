module
public import Linear.NativeComplementaryPolynomialSheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- Degree-a to degree-b ORIGINAL sheaf multiplication, with a=l+b.
The source cast is genuine equality transport, not duality coordinates. -/
def coordinateNativeDegreePolynomialSheafMap (a b l : ℕ) (h : a = l+b)
    (p : homogeneousSubmodule σ K l) :
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a:ℤ)-Fintype.card σ) ⟶
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-(b:ℤ)-Fintype.card σ) :=
  coordinateNativeSheafDegreeCast (congrArg (fun q : ℕ => -(q:ℤ)-Fintype.card σ) h) ≫
    coordinateNativeComplementaryPolynomialSheafMap l b p

/-- Actual transpose of homogeneous polynomial multiplication, with the
same proved source-degree equality. -/
def projectiveHomogeneousDegreeMultiplyDual {B : Type} [CommRing B]
    (a b l : ℕ) (h : a = l+b) (p : homogeneousSubmodule σ B l) :
    ModuleCat.of B (Module.Dual B (homogeneousSubmodule σ B a)) ⟶
    ModuleCat.of B (Module.Dual B (homogeneousSubmodule σ B b)) :=
  eqToHom (congrArg (fun q => ModuleCat.of B (Module.Dual B (homogeneousSubmodule σ B q))) h) ≫
    ModuleCat.ofHom (projectiveHomogeneousMultiplyDual l b p)

/-- The source-degree transports on both sides actually commute with the
native top-Cech duality isomorphisms. -/
theorem coordinateNativeDegreePolynomialSheafMap_top_duality (a b l n : ℕ)
    (hc : Fintype.card σ = n+2) (h : a = l+b) (p : homogeneousSubmodule σ K l) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeDegreePolynomialSheafMap a b l h p) ≫
        (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) b n hc).hom =
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) a n hc).hom ≫
      projectiveHomogeneousDegreeMultiplyDual a b l h
        (projectiveHomogeneousCoefficientMap
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom l p) := by
  subst a
  simp only [coordinateNativeDegreePolynomialSheafMap, coordinateNativeSheafDegreeCast,
    projectiveHomogeneousDegreeMultiplyDual, eqToHom_refl, Category.id_comp]
  exact coordinateNativeComplementaryPolynomialSheafMap_top_duality l b n hc p

end MvPolynomial
