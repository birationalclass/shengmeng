module
public import Linear.CochainSourceLiftClasses
public import Linear.CochainSourceLiftComponentRecurrence
public import Linear.InjectiveCochainCocycleSourceClass
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

/-- SAME source quotient augmentation at its proved terminal position. -/
def cochainSourceTerminalMap {K : CochainComplex A ℤ} {E : A} (r : ℕ)
    (g : K.opcycles 0 ⟶ E) : K.opcycles (cochainSourceDegree r r) ⟶ E :=
  eqToHom (congrArg (fun j : ℤ => K.opcycles j)
    (show cochainSourceDegree r r=0 by rw [cochainSourceDegree_eq]; omega)) ≫ g

theorem cochainSourceTerminalMap_isIso {K : CochainComplex A ℤ} {E : A} (r : ℕ)
    (g : K.opcycles 0 ⟶ E) [IsIso g] : IsIso (cochainSourceTerminalMap r g) := by
  unfold cochainSourceTerminalMap
  infer_instance

/-- The terminal ACTUAL cocycle is exactly pullback of SAME coefficient
cocycle,including the endpoint transport and native degree-zero Ext action. -/
theorem cochainSourceLiftClass_terminal {K : CochainComplex A ℤ} {E N : A}
    (I : InjectiveResolution N) (r : ℕ)
    (t : Cochain K I.cochainComplex ((r : ℤ)-1)) (g : K.opcycles 0 ⟶ E)
    (f : E ⟶ I.cochainComplex.X (r : ℤ))
    (hf : f ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
    (har : cochainSourceTerminalMorph r (g ≫ f) ≫
      I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
    (hB : cochainSourceLiftRecurrence r t (cochainSourceTerminalMorph r (g ≫ f))) :
    cochainSourceLiftClass I r t (cochainSourceTerminalMorph r (g ≫ f)) har hB r le_rfl =
      (Ext.mk₀ (cochainSourceTerminalMap r g)).comp
        (I.extEquivCohomologyClass.symm (CohomologyClass.mk
          (Cocycle.fromSingleMk f (zero_add _) ((r : ℤ)+1) rfl hf))) (zero_add r) := by
  rw [injectiveCochainCocycleClass_precompose]
  rw [← Cocycle.fromSingleMk_precomp (cochainSourceTerminalMap r g) f
    (zero_add _) ((r : ℤ)+1) rfl hf]
  simp only [cochainSourceLiftClass,cochainSourceLiftMorph_last,cochainSourceTerminalMorph,
    cochainSourceTerminalMap,Category.assoc]

end LinearStudy
