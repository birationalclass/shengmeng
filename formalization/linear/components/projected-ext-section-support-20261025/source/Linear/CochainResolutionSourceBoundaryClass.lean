module
public import Linear.CochainResolutionSourceBoundaryFamily
public import Linear.CochainSourceLiftTerminalClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- CONSTRUCT EVERY original source cocycle and PROVE that their actual
native iterated boundary gives SAME original roof class. Its initial morphism
projects to SAME top functional,and the terminal source map is canonical.
No class identity,source-lift or recurrence premise remains. -/
theorem cochainResolutionSourceBoundaryClass_exists
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0)
    (I : InjectiveResolution N) :
    ∃ (f : E ⟶ I.cochainComplex.X (r : ℤ))
      (hf : f ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
      (t : Cochain K I.cochainComplex ((r : ℤ)-1))
      (har : cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f) ≫
        I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
      (hB : cochainSourceLiftRecurrence r t
        (cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f))),
      cochainResolutionTopExtClass K r alpha a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk
          (Cocycle.fromSingleMk f (zero_add _) ((r : ℤ)+1) rfl hf)) ∧
      K.pOpcycles (-(r : ℤ)) ≫ cochainSourceLiftMorph r t
        (cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f)) 0 (Nat.zero_le r) =
        a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0 ∧
      cochainOpcycleIteratedBoundary K r alpha r le_rfl
        (cochainSourceLiftClass I r t
          (cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f)) har hB 0 (Nat.zero_le r)) =
        (Ext.mk₀ (cochainSourceTerminalMap r (cochainAugmentationOpcycle alpha))).comp
          (cochainResolutionTopExtClass K r alpha a ha) (zero_add r) := by
  obtain ⟨f,hf,t,hclass,htop,hB⟩ :=
    cochainResolutionSourceBoundaryFamily_exists K r hr alpha a ha I
  have har : cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f) ≫
      I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0 := by
    simp only [cochainSourceTerminalMorph,Category.assoc,hf,comp_zero]
  refine ⟨f,hf,t,har,hB,hclass,?_,?_⟩
  · rw [cochainSourceLiftMorph_lt r t _ 0 (Nat.zero_le r) hr]
    dsimp only [cochainSourceDegree]
    rw [← Category.assoc,HomologicalComplex.p_fromOpcycles]
    exact htop
  · rw [cochainSourceLiftClass_iterated,hclass]
    exact cochainSourceLiftClass_terminal I r t (cochainAugmentationOpcycle alpha) f hf har hB

end LinearStudy
