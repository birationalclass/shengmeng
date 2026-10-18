module
public import Linear.CochainResolutionInjectiveCocycle
public import Linear.CochainClassEqBoundary
public import Linear.CochainSourceLiftSigns
public import Linear.CochainResolutionTopHomotopyEquations
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

/-- CONSTRUCT ACTUAL source lifts with POSITIVE lifting equations in every
original degree. Normalize the CONSTRUCTED homotopy signs;retain the SAME
roof class,original top functional and actual augmentation. -/
theorem cochainResolutionSourceLiftEquations_exists
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0)
    (I : InjectiveResolution N) :
    ∃ (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) I.cochainComplex (r : ℤ))
      (t : Cochain K I.cochainComplex ((r : ℤ)-1)),
      cochainResolutionTopExtClass K r alpha a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c) ∧
      K.d (-(r : ℤ)) (-(r : ℤ)+1) ≫
          t.v (-(r : ℤ)+1) 0 (by omega) =
        (a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0) ∧
      (∀ j : ℤ,-(r : ℤ) < j → j < 0 →
        t.v j (j+(r : ℤ)-1) (by omega) ≫ I.cochainComplex.d (j+(r : ℤ)-1) (j+(r : ℤ)) =
          K.d j (j+1) ≫ t.v (j+1) (j+(r : ℤ)) (by omega)) ∧
      t.v 0 ((r : ℤ)-1) (zero_add _) ≫ I.cochainComplex.d ((r : ℤ)-1) (r : ℤ) =
        alpha.f 0 ≫ c.val.v 0 (r : ℤ) (zero_add _) := by
  obtain ⟨c,t,hclass,htop,hmid,hbot⟩ :=
    cochainResolutionTopHomotopyEquations_exists K r hr alpha a ha I
  refine ⟨c,cochainSourceLiftSigns (r : ℤ) t,hclass,?_,?_,?_⟩
  · exact cochainSourceLiftSigns_top (r : ℤ) t _ htop
  · intro j hj hj0
    exact cochainSourceLiftSigns_middle (r : ℤ) j t (hmid j hj hj0)
  · exact cochainSourceLiftSigns_bottom (r : ℤ) t _ _ hbot

end LinearStudy
