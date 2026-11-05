module
public import Linear.NativeGradedPolynomialEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory
variable {R : Type} [CommRing R] {σ : Type}

/-- The ORIGINAL polynomial multiplication with the ACTUAL target-degree
equality transport. This is constructed before taking any dual. -/
def projectiveHomogeneousDegreeMultiply (a b l : ℕ) (h : a=l+b)
    (p : homogeneousSubmodule σ R l) :
    ModuleCat.of R (homogeneousSubmodule σ R b) ⟶
      ModuleCat.of R (homogeneousSubmodule σ R a) :=
  ModuleCat.ofHom (projectiveHomogeneousMultiply l b p) ≫
    eqToHom (congrArg (fun q => ModuleCat.of R (homogeneousSubmodule σ R q)) h.symm)

/-- Dualizing ACTUAL degree-transported multiplication gives exactly
the ORIGINAL degree-transported multiplication transpose. -/
theorem projectiveHomogeneousDegreeMultiply_dual (a b l : ℕ) (h : a=l+b)
    (p : homogeneousSubmodule σ R l) :
    ModuleCat.ofHom (projectiveHomogeneousDegreeMultiply a b l h p).hom.dualMap =
      projectiveHomogeneousDegreeMultiplyDual a b l h p := by
  subst a
  simp only [projectiveHomogeneousDegreeMultiply,projectiveHomogeneousDegreeMultiplyDual,
    eqToHom_refl,Category.comp_id,Category.id_comp]
  rfl

/-- The ORIGINAL polynomial value is preserved by target-degree transport. -/
theorem projectiveHomogeneousDegreeMultiply_coe (a b l : ℕ) (h : a=l+b)
    (p : homogeneousSubmodule σ R l) (q : homogeneousSubmodule σ R b) :
    (projectiveHomogeneousDegreeMultiply a b l h p q).1 = p.1*q.1 := by
  subst a
  rfl

/-- The actual original graded polynomial multiplication entry.
If the multiplication degree is negative,the ORIGINAL entry is zero. -/
def projectiveHomogeneousGradedPolynomialMultiplyEntry (a b : ℕ)
    (p : homogeneousSubmodule σ R (a-b)) :
    ModuleCat.of R (homogeneousSubmodule σ R b) ⟶
      ModuleCat.of R (homogeneousSubmodule σ R a) :=
  if h : b ≤ a then
    projectiveHomogeneousDegreeMultiply a b (a-b) (Nat.sub_add_cancel h).symm p
  else 0

/-- Every nonnegative original multiplication entry has its ORIGINAL
polynomial product value,not a transported-duality definition. -/
theorem projectiveHomogeneousGradedPolynomialMultiplyEntry_coe (a b : ℕ)
    (p : homogeneousSubmodule σ R (a-b)) (q : homogeneousSubmodule σ R b) (h : b≤a) :
    (projectiveHomogeneousGradedPolynomialMultiplyEntry a b p q).1 = p.1*q.1 := by
  simp only [projectiveHomogeneousGradedPolynomialMultiplyEntry,dite_eq_left h]
  exact projectiveHomogeneousDegreeMultiply_coe a b (a-b) (Nat.sub_add_cancel h).symm p q

/-- The original multiplication entry is ZERO in negative multiplying degree. -/
theorem projectiveHomogeneousGradedPolynomialMultiplyEntry_of_lt (a b : ℕ)
    (p : homogeneousSubmodule σ R (a-b)) (h : a<b) :
    projectiveHomogeneousGradedPolynomialMultiplyEntry a b p = 0 := by
  simp only [projectiveHomogeneousGradedPolynomialMultiplyEntry,dite_eq_right (not_le_of_gt h)]

/-- The ORIGINAL graded dual entry is proved to be the dual of the
ACTUAL ORIGINAL graded multiplication entry,including its zero branch. -/
theorem projectiveHomogeneousGradedPolynomialMultiplyEntry_dual (a b : ℕ)
    (p : homogeneousSubmodule σ R (a-b)) :
    ModuleCat.ofHom (projectiveHomogeneousGradedPolynomialMultiplyEntry a b p).hom.dualMap =
      projectiveHomogeneousGradedPolynomialDualEntry a b p := by
  by_cases h : b≤a
  · simp only [projectiveHomogeneousGradedPolynomialMultiplyEntry,
      projectiveHomogeneousGradedPolynomialDualEntry,dite_eq_left h]
    exact projectiveHomogeneousDegreeMultiply_dual a b (a-b) (Nat.sub_add_cancel h).symm p
  · simp only [projectiveHomogeneousGradedPolynomialMultiplyEntry,
      projectiveHomogeneousGradedPolynomialDualEntry,dite_eq_right h]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro q
    change φ 0 = 0
    exact map_zero φ

end MvPolynomial
