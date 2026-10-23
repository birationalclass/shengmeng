module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- Equal actual cocycle classes have a constructed actual cochain difference. -/
theorem cochainClassEq_boundary_exists {K L : CochainComplex A ℤ} (q : ℤ)
    (a b : Cocycle K L q) (h : CohomologyClass.mk a = CohomologyClass.mk b) :
    ∃ t : Cochain K L (q-1),δ (q-1) q t = a.val-b.val := by
  have hz : CohomologyClass.mk (a-b) = 0 := by
    rw [CohomologyClass.mk_sub,h,sub_self]
  exact (mem_coboundaries_iff (a-b) (q-1) (by omega)).mp
    ((CohomologyClass.mk_eq_zero_iff (a-b)).mp hz)

end LinearStudy
