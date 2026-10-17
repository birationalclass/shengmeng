module
public import Linear.CochainSourceLiftRecurrence
public import Linear.CochainOpcycleInjectiveBoundaryComponents
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Native ACTUAL Ext class of EACH constructed source quotient cocycle. -/
def cochainSourceLiftClass {K : CochainComplex A ℤ} {N : A} (I : InjectiveResolution N)
    (r : ℕ) (t : Cochain K I.cochainComplex ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ I.cochainComplex.X (r : ℤ))
    (har : ar ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
    (hB : cochainSourceLiftRecurrence r t ar) (n : ℕ) (hn : n ≤ r) :
    Ext (K.opcycles (cochainSourceDegree r n)) N n :=
  I.extEquivCohomologyClass.symm (CohomologyClass.mk
    (Cocycle.fromSingleMk (cochainSourceLiftMorph r t ar n hn) (zero_add _)
      ((n : ℤ)+1) rfl (cochainSourceLiftMorph_closed r t ar har hB n hn)))

/-- EVERY actual next boundary maps the SAME constructed quotient cocycle
to the next one;its short exactness is derived from original augmentation. -/
theorem cochainSourceLiftClass_boundary
    (K : CochainComplex A ℤ) {E N : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (I : InjectiveResolution N) (r : ℕ)
    (t : Cochain K I.cochainComplex ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ I.cochainComplex.X (r : ℤ))
    (har : ar ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
    (hB : cochainSourceLiftRecurrence r t ar) (n : ℕ) (hn : n < r) :
    Ext.δ (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
      (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega)))
      n (n+1) rfl (cochainSourceLiftClass I r t ar har hB n (by omega)) =
      cochainSourceLiftClass I r t ar har hB (n+1) (by omega) := by
  unfold cochainSourceLiftClass
  apply shortExactInjectiveExtBoundary_components (cochainOpcycleSourceSequence K (cochainSourceDegree r n))
    (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
      (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega)))
    I n _ _ (t.v (cochainSourceDegree r (n+1)) (n : ℤ)
      (by rw [cochainSourceDegree_eq]; push_cast; omega)) _ _
  · dsimp only [cochainOpcycleSourceSequence]
    rw [cochainSourceLiftMorph_lt r t ar n (by omega) hn]
    rfl
  · exact hB n hn

/-- Iterate through EVERY original source quotient. The terminal class is
PROVED from actual native boundaries,not supplied as a desired identity. -/
theorem cochainSourceLiftClass_iterated
    (K : CochainComplex A ℤ) {E N : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (I : InjectiveResolution N) (r : ℕ)
    (t : Cochain K I.cochainComplex ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ I.cochainComplex.X (r : ℤ))
    (har : ar ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
    (hB : cochainSourceLiftRecurrence r t ar) (n : ℕ) (hn : n ≤ r) :
    cochainOpcycleIteratedBoundary K r alpha n hn
      (cochainSourceLiftClass I r t ar har hB 0 (Nat.zero_le r)) =
      cochainSourceLiftClass I r t ar har hB n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cochainOpcycleIteratedBoundary_succ,ih (by omega)]
    exact cochainSourceLiftClass_boundary K alpha I r t ar har hB n (by omega)

end LinearStudy
