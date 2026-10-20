module
public import Linear.CochainResolutionInjectiveCocycle
public import Linear.CochainClassEqBoundary
public import Linear.CochainAugmentedTopHomotopyComponents
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

/-- CONSTRUCT the SAME roof representative and source homotopy,then derive
ALL actual lifting equations from its top,middle,and bottom components.
No component equation or class identification is a premise. -/
theorem cochainResolutionTopHomotopyEquations_exists
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0)
    (I : InjectiveResolution N) :
    ∃ (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) I.cochainComplex (r : ℤ))
      (t : Cochain K I.cochainComplex ((r : ℤ)-1)),
      cochainResolutionTopExtClass K r alpha a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c) ∧
      (r : ℤ).negOnePow • K.d (-(r : ℤ)) (-(r : ℤ)+1) ≫
          t.v (-(r : ℤ)+1) 0 (by omega) =
        -(a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0) ∧
      (∀ j : ℤ,-(r : ℤ) < j → j < 0 →
        t.v j (j+(r : ℤ)-1) (by omega) ≫ I.cochainComplex.d (j+(r : ℤ)-1) (j+(r : ℤ)) +
          (r : ℤ).negOnePow • K.d j (j+1) ≫ t.v (j+1) (j+(r : ℤ)) (by omega) = 0) ∧
      t.v 0 ((r : ℤ)-1) (zero_add _) ≫ I.cochainComplex.d ((r : ℤ)-1) (r : ℤ) =
        alpha.f 0 ≫ c.val.v 0 (r : ℤ) (zero_add _) := by
  let beta := Cocycle.toSingleMk a (show -(r : ℤ)+(r : ℤ)=0 by omega)
    (-(r : ℤ)-1) (by omega) ha
  obtain ⟨c,hc,hroof⟩ := cochainResolutionInjectiveCocycle_exists K r alpha beta I
  obtain ⟨t,ht⟩ := cochainClassEq_boundary_exists (r : ℤ) _ _ hc
  change δ ((r : ℤ)-1) (r : ℤ) t = (c.precomp alpha).val -
    (Cochain.toSingleMk a (show -(r : ℤ)+(r : ℤ)=0 by omega)).comp
      (Cochain.ofHom I.ι') (add_zero (r : ℤ)) at ht
  refine ⟨c,t,?_,?_,?_,?_⟩
  · simpa only [cochainResolutionTopExtClass,beta] using hroof
  · exact cochainAugmentedTopHomotopy_top (r : ℤ) (by omega) alpha c a I.ι' t ht
      (I.cochainComplex.isZero_of_isStrictlyGE 0 (-1) (by omega))
  · intro j hj hj0
    exact cochainAugmentedTopHomotopy_middle (r : ℤ) j alpha c a I.ι' t ht (by omega) (by omega)
  · exact cochainAugmentedTopHomotopy_bottom (r : ℤ) (by omega) alpha c a I.ι' t ht
      ((K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)

end LinearStudy
