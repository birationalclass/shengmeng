module
public import Linear.CochainSourceLiftRecurrence
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

/-- ACTUAL terminal component,transported only by the proved source endpoint. -/
def cochainSourceTerminalMorph {K L : CochainComplex A ℤ} (r : ℕ)
    (g : K.opcycles 0 ⟶ L.X (r : ℤ)) :
    K.opcycles (cochainSourceDegree r r) ⟶ L.X (r : ℤ) :=
  eqToHom (congrArg (fun j : ℤ => K.opcycles j) (show cochainSourceDegree r r=0 by rw [cochainSourceDegree_eq]; omega)) ≫ g

/-- The positive middle/bottom equations DERIVE the actual finite quotient
recurrence. There is NO class identity or connecting-map premise. -/
theorem cochainSourceLiftRecurrence_of_components
    {K L : CochainComplex A ℤ} (r : ℕ)
    (t : Cochain K L ((r : ℤ)-1)) (g : K.opcycles 0 ⟶ L.X (r : ℤ))
    (hmid : ∀ j : ℤ,-(r : ℤ) < j → j < 0 →
      t.v j (j+(r : ℤ)-1) (by omega) ≫ L.d (j+(r : ℤ)-1) (j+(r : ℤ)) =
        K.d j (j+1) ≫ t.v (j+1) (j+(r : ℤ)) (by omega))
    (hbot : t.v 0 ((r : ℤ)-1) (zero_add _) ≫ L.d ((r : ℤ)-1) (r : ℤ) =
      K.pOpcycles 0 ≫ g) :
    cochainSourceLiftRecurrence r t (cochainSourceTerminalMorph r g) := by
  intro n hn
  by_cases hnext : n+1 < r
  · rw [cochainSourceLiftMorph_lt r t _ (n+1) (by omega) hnext,
      ← Category.assoc,HomologicalComplex.p_fromOpcycles]
    have hj : -(r : ℤ) < cochainSourceDegree r (n+1) := by rw [cochainSourceDegree_eq]; omega
    have hj0 : cochainSourceDegree r (n+1) < 0 := by rw [cochainSourceDegree_eq]; omega
    have hm := hmid (cochainSourceDegree r (n+1)) hj hj0
    have hq : cochainSourceDegree r (n+1)+(r : ℤ)-1=(n : ℤ) := by
      rw [cochainSourceDegree_eq]; push_cast; omega
    have hq' : cochainSourceDegree r (n+1)+(r : ℤ)=((n+1 : ℕ) : ℤ) := by
      rw [cochainSourceDegree_eq]; omega
    convert! hm using 1 <;> congr! 3 <;> simp_all only [cochainSourceDegree_eq,Nat.cast_add,Nat.cast_one] <;> omega
  · have he : r = n+1 := by omega
    subst r
    rw [cochainSourceLiftMorph_last]
    simp only [cochainSourceTerminalMorph]
    convert! hbot using 1 <;> congr! 3 <;> simp_all only [cochainSourceDegree_eq,Nat.cast_add,Nat.cast_one,neg_add_cancel,eqToHom_refl,Category.id_comp] <;> first | omega | exact CategoryTheory.eqToHom_comp_heq _ _

end LinearStudy
