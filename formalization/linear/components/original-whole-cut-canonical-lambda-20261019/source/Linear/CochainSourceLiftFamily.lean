module
public import Linear.CochainOpcycleIteratedBoundary
public import Linear.CochainResolutionSourceLiftEquations
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

/-- ACTUAL quotient components from source lifts;the last component is the
specified actual terminal morphism,with no class identity in the construction. -/
def cochainSourceLiftMorph {K L : CochainComplex A ℤ} (r : ℕ)
    (t : Cochain K L ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ L.X (r : ℤ))
    (n : ℕ) (hn : n ≤ r) : K.opcycles (cochainSourceDegree r n) ⟶ L.X (n : ℤ) :=
  if h : n < r then
    K.fromOpcycles (cochainSourceDegree r n) (cochainSourceDegree r (n+1)) ≫
      t.v (cochainSourceDegree r (n+1)) (n : ℤ)
        (by rw [cochainSourceDegree_eq]; push_cast; omega)
  else by
    have he : n = r := by omega
    subst n
    exact ar

/-- The nonterminal term retains SAME actual source lift. -/
theorem cochainSourceLiftMorph_lt {K L : CochainComplex A ℤ} (r : ℕ)
    (t : Cochain K L ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ L.X (r : ℤ))
    (n : ℕ) (hn : n ≤ r) (h : n < r) :
    cochainSourceLiftMorph r t ar n hn =
      K.fromOpcycles (cochainSourceDegree r n) (cochainSourceDegree r (n+1)) ≫
        t.v (cochainSourceDegree r (n+1)) (n : ℤ)
          (by rw [cochainSourceDegree_eq]; push_cast; omega) := by
  simp only [cochainSourceLiftMorph,dite_eq_left h]

/-- The terminal term is exactly the original terminal morphism. -/
theorem cochainSourceLiftMorph_last {K L : CochainComplex A ℤ} (r : ℕ)
    (t : Cochain K L ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ L.X (r : ℤ)) :
    cochainSourceLiftMorph r t ar r le_rfl = ar := by
  simp only [cochainSourceLiftMorph,dite_eq_right (not_lt_of_ge (le_refl r))]

end LinearStudy
