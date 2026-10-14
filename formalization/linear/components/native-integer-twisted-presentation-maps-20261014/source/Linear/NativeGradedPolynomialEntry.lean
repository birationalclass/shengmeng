module
public import Linear.NativeGradedPolynomialDegreeTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- An ORIGINAL graded polynomial matrix entry. If b<=a, multiply by
p of degree a-b. If a<b, this entry is zero. Thus no ordering of all
source and target twists is imposed on the finite matrix. -/
def coordinateNativeGradedPolynomialEntry (a b : ℕ)
    (p : homogeneousSubmodule σ K (a-b)) :
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a:ℤ)-Fintype.card σ) ⟶
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-(b:ℤ)-Fintype.card σ) :=
  if h : b ≤ a then
    coordinateNativeDegreePolynomialSheafMap a b (a-b) (Nat.sub_add_cancel h).symm p
  else 0

/-- The actual homogeneous multiplication transpose for the same graded
entry. Negative multiplying degrees are represented by zero entries. -/
def projectiveHomogeneousGradedPolynomialDualEntry {B : Type} [CommRing B]
    (a b : ℕ) (p : homogeneousSubmodule σ B (a-b)) :
    ModuleCat.of B (Module.Dual B (homogeneousSubmodule σ B a)) ⟶
    ModuleCat.of B (Module.Dual B (homogeneousSubmodule σ B b)) :=
  if h : b ≤ a then
    projectiveHomogeneousDegreeMultiplyDual a b (a-b) (Nat.sub_add_cancel h).symm p
  else 0

theorem coordinateNativeGradedPolynomialEntry_of_lt (a b : ℕ)
    (p : homogeneousSubmodule σ K (a-b)) (h : a < b) :
    coordinateNativeGradedPolynomialEntry a b p = 0 := by
  simp only [coordinateNativeGradedPolynomialEntry, dite_eq_right (not_le_of_gt h)]

omit [Fintype σ] [LinearOrder σ] in
theorem projectiveHomogeneousGradedPolynomialDualEntry_of_lt {B : Type} [CommRing B]
    (a b : ℕ) (p : homogeneousSubmodule σ B (a-b)) (h : a < b) :
    projectiveHomogeneousGradedPolynomialDualEntry a b p = 0 := by
  simp only [projectiveHomogeneousGradedPolynomialDualEntry, dite_eq_right (not_le_of_gt h)]

/-- Every actual graded matrix entry satisfies the native top-Cech duality
square. This includes the proved zero case when its polynomial degree
would be negative; it does not assume a uniform twist. -/
theorem coordinateNativeGradedPolynomialEntry_top_duality (a b n : ℕ)
    (hc : Fintype.card σ = n+2) (p : homogeneousSubmodule σ K (a-b)) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (coordinateNativeGradedPolynomialEntry a b p) ≫
        (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) b n hc).hom =
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) a n hc).hom ≫
      projectiveHomogeneousGradedPolynomialDualEntry a b
        (projectiveHomogeneousCoefficientMap
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom (a-b) p) := by
  by_cases h : b ≤ a
  · simp only [coordinateNativeGradedPolynomialEntry,
      projectiveHomogeneousGradedPolynomialDualEntry, dite_eq_left h]
    exact coordinateNativeDegreePolynomialSheafMap_top_duality a b (a-b) n hc
      (Nat.sub_add_cancel h).symm p
  · simp only [coordinateNativeGradedPolynomialEntry,
      projectiveHomogeneousGradedPolynomialDualEntry, dite_eq_right h,
      Functor.map_zero, zero_comp, comp_zero]

end MvPolynomial
