module
public import Linear.CochainSourceLiftComponentRecurrence
public import Linear.CochainAugmentationOpcycle
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

/-- For SAME original augmentation and top functional,CONSTRUCT the actual
terminal cocycle and source lift recurrence in ALL successive quotients.
No recurrence,representative,class identity or projectivity input is supplied. -/
theorem cochainResolutionSourceBoundaryFamily_exists
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0)
    (I : InjectiveResolution N) :
    ∃ (f : E ⟶ I.cochainComplex.X (r : ℤ))
      (hf : f ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
      (t : Cochain K I.cochainComplex ((r : ℤ)-1)),
      cochainResolutionTopExtClass K r alpha a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk
          (Cocycle.fromSingleMk f (zero_add _) ((r : ℤ)+1) rfl hf)) ∧
      K.d (-(r : ℤ)) (-(r : ℤ)+1) ≫ t.v (-(r : ℤ)+1) 0 (by omega) =
        a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0 ∧
      cochainSourceLiftRecurrence r t
        (cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f)) := by
  obtain ⟨c,t,hclass,htop,hmid,hbot⟩ :=
    cochainResolutionSourceLiftEquations_exists K r hr alpha a ha I
  obtain ⟨f,hf,hc⟩ := Cocycle.fromSingleMk_surjective c (r : ℤ) (zero_add _) ((r : ℤ)+1) rfl
  refine ⟨f,hf,t,?_,htop,?_⟩
  · rw [hc]
    exact hclass
  · apply cochainSourceLiftRecurrence_of_components r t _ hmid
    rw [← Category.assoc,cochainAugmentationOpcycle_projection,Category.assoc]
    rw [← hc] at hbot
    change t.v 0 ((r : ℤ)-1) (zero_add _) ≫ I.cochainComplex.d ((r : ℤ)-1) (r : ℤ) =
      alpha.f 0 ≫ (Cochain.fromSingleMk f (zero_add _)).v 0 (r : ℤ) (zero_add _) at hbot
    simpa only [Cochain.fromSingleMk_v,Category.assoc] using hbot

end LinearStudy
