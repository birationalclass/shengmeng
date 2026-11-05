module
public import Linear.ProjectiveHomogeneousDualCoefficientEquiv
public import Linear.ProjectiveCanonicalDualCoefficientEquiv
public import Linear.NativeGradedPolynomialEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}
attribute [local instance] projectiveCoefficientInverseForward projectiveCoefficientInverseBackward

/-- Original degree equality transport commutes with the constructed
homogeneous dual coefficient equivalence; no comparison square is assumed. -/
theorem projectiveHomogeneousDualCoefficientEquiv_degreeMultiply
    (e : R ≃+* S) (a b l : ℕ) (h : a = l+b)
    (p : homogeneousSubmodule σ R l)
    (φ : Module.Dual R (homogeneousSubmodule σ R a)) :
    projectiveHomogeneousDualCoefficientEquiv e b
        (projectiveHomogeneousDegreeMultiplyDual a b l h p φ) =
      projectiveHomogeneousDegreeMultiplyDual a b l h
        (projectiveHomogeneousCoefficientEquiv e l p)
        (projectiveHomogeneousDualCoefficientEquiv e a φ) := by
  subst a
  simp only [projectiveHomogeneousDegreeMultiplyDual,eqToHom_refl,Category.id_comp]
  exact projectiveHomogeneousDualCoefficientEquiv_multiply e l b p φ

/-- Every actual original graded polynomial dual entry commutes with
coefficient change. This includes the negative-degree ZERO entry. -/
theorem projectiveHomogeneousDualCoefficientEquiv_gradedEntry
    (e : R ≃+* S) (a b : ℕ) (p : homogeneousSubmodule σ R (a-b))
    (φ : Module.Dual R (homogeneousSubmodule σ R a)) :
    projectiveHomogeneousDualCoefficientEquiv e b
        (projectiveHomogeneousGradedPolynomialDualEntry a b p φ) =
      projectiveHomogeneousGradedPolynomialDualEntry a b
        (projectiveHomogeneousCoefficientEquiv e (a-b) p)
        (projectiveHomogeneousDualCoefficientEquiv e a φ) := by
  by_cases h : b ≤ a
  · simp only [projectiveHomogeneousGradedPolynomialDualEntry,dite_eq_left h]
    exact projectiveHomogeneousDualCoefficientEquiv_degreeMultiply e a b (a-b)
      (Nat.sub_add_cancel h).symm p φ
  · simp only [projectiveHomogeneousGradedPolynomialDualEntry,dite_eq_right h]
    change projectiveHomogeneousDualCoefficientEquiv e b 0 = 0
    exact map_zero _

attribute [local instance] coordinateCanonicalCoefficientInverseForward coordinateCanonicalCoefficientInverseBackward

/-- The ACTUAL affine canonical coefficients commute with every actual
graded dual matrix entry,including the proved zero case. No chosen scalar
comparison is supplied. This is an entry theorem,not yet a cokernel theorem. -/
theorem coordinateCanonicalHomogeneousDualCoefficientEquiv_gradedEntry
    (K : Type) [CommRing K] (a b : ℕ)
    (p : homogeneousSubmodule σ K (a-b))
    (φ : Module.Dual K (homogeneousSubmodule σ K a)) :
    coordinateCanonicalHomogeneousDualCoefficientEquiv K b
        (projectiveHomogeneousGradedPolynomialDualEntry a b p φ) =
      projectiveHomogeneousGradedPolynomialDualEntry a b
        (coordinateCanonicalHomogeneousCoefficientEquiv K (a-b) p)
        (coordinateCanonicalHomogeneousDualCoefficientEquiv K a φ) :=
  projectiveHomogeneousDualCoefficientEquiv_gradedEntry
    (coordinateCanonicalCoefficientRingEquiv K) a b p φ

end MvPolynomial
