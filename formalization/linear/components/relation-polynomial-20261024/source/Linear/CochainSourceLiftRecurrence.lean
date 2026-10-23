module
public import Linear.CochainSourceLiftFamily
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- ACTUAL morphism recursion for SAME quotient components,not a class identity. -/
def cochainSourceLiftRecurrence {K L : CochainComplex A ℤ} (r : ℕ)
    (t : Cochain K L ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ L.X (r : ℤ)) : Prop :=
  ∀ (n : ℕ) (hn : n < r),
    t.v (cochainSourceDegree r (n+1)) (n : ℤ)
        (by rw [cochainSourceDegree_eq]; push_cast; omega) ≫
        L.d (n : ℤ) ((n+1 : ℕ) : ℤ) =
      K.pOpcycles (cochainSourceDegree r (n+1)) ≫
        cochainSourceLiftMorph r t ar (n+1) (by omega)

/-- Actual positive lifting recursion DERIVES closure of EVERY component. -/
theorem cochainSourceLiftMorph_closed {K L : CochainComplex A ℤ} (r : ℕ)
    (t : Cochain K L ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ L.X (r : ℤ))
    (har : ar ≫ L.d (r : ℤ) ((r : ℤ)+1) = 0)
    (hB : cochainSourceLiftRecurrence r t ar) (n : ℕ) (hn : n ≤ r) :
    cochainSourceLiftMorph r t ar n hn ≫ L.d (n : ℤ) ((n : ℤ)+1) = 0 := by
  by_cases h : n < r
  · rw [cochainSourceLiftMorph_lt r t ar n hn h]
    have hb := hB n h
    rw [show ((n : ℤ)+1)=((n+1 : ℕ) : ℤ) by omega,Category.assoc,hb,← Category.assoc]
    simpa only [cochainSourceDegree,cochainOpcycleSourceSequence,Category.assoc,zero_comp]
      using (cochainOpcycleSourceSequence K (cochainSourceDegree r n)).zero_assoc
        (cochainSourceLiftMorph r t ar (n+1) (by omega))
  · have he : n = r := by omega
    subst n
    rw [cochainSourceLiftMorph_last]
    exact har

end LinearStudy
