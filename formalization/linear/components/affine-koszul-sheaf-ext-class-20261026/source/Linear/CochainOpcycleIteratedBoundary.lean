module
public import Linear.CochainOpcycleSourceSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Actual successive source positions,starting at ORIGINAL top degree. -/
def cochainSourceDegree (r : ℕ) : ℕ → ℤ
  | 0 => -(r : ℤ)
  | n+1 => cochainSourceDegree r n + 1

theorem cochainSourceDegree_eq (r n : ℕ) :
    cochainSourceDegree r n = -(r : ℤ)+(n : ℤ) := by
  induction n with
  | zero => simp [cochainSourceDegree]
  | succ n ih => simp only [cochainSourceDegree,ih,Nat.cast_add,Nat.cast_one]; omega

/-- Iterate ONLY actual native source boundaries,whose short exactness is
DERIVED from SAME quasi-isomorphic augmentation. No projectivity assumption. -/
def cochainOpcycleIteratedBoundary (K : CochainComplex A ℤ) {E N : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n ≤ r) :
    Ext (K.opcycles (cochainSourceDegree r 0)) N 0 →+
      Ext (K.opcycles (cochainSourceDegree r n)) N n := by
  induction n with
  | zero => exact AddMonoidHom.id _
  | succ n ih =>
    have hj : cochainSourceDegree r n < 0 := by rw [cochainSourceDegree_eq]; omega
    exact (Ext.δ (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
      (cochainAugmentation_exactAt_negative K alpha _ hj)) n (n+1) rfl).comp (ih (by omega))

/-- The recursive map really is the SAME next native boundary. -/
theorem cochainOpcycleIteratedBoundary_succ
    (K : CochainComplex A ℤ) {E N : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n+1 ≤ r) (x : Ext (K.opcycles (cochainSourceDegree r 0)) N 0) :
    cochainOpcycleIteratedBoundary K r alpha (n+1) hn x =
      Ext.δ (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
        (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega)))
        n (n+1) rfl (cochainOpcycleIteratedBoundary K r alpha n (by omega) x) := by
  rfl

end LinearStudy
