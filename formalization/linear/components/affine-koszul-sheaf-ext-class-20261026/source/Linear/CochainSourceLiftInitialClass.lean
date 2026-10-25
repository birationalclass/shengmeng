module
public import Linear.CochainSourceLiftClasses
public import Linear.InjectiveCochainDegreeZeroClass
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

/-- Actual initial component equals the original morphism followed by the
coefficient augmentation,so its native Ext class is EXACTLY Ext.mk0. -/
theorem cochainSourceLiftClass_initial {K : CochainComplex A ℤ} {N : A}
    (I : InjectiveResolution N) (r : ℕ)
    (t : Cochain K I.cochainComplex ((r : ℤ)-1))
    (ar : K.opcycles (cochainSourceDegree r r) ⟶ I.cochainComplex.X (r : ℤ))
    (har : ar ≫ I.cochainComplex.d (r : ℤ) ((r : ℤ)+1) = 0)
    (hB : cochainSourceLiftRecurrence r t ar)
    (g : K.opcycles (cochainSourceDegree r 0) ⟶ N)
    (hg : cochainSourceLiftMorph r t ar 0 (Nat.zero_le r) =
      g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0) :
    cochainSourceLiftClass I r t ar har hB 0 (Nat.zero_le r) = Ext.mk₀ g := by
  have hclosed := cochainSourceLiftMorph_closed r t ar har hB 0 (Nat.zero_le r)
  have hgc : (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0) ≫
      I.cochainComplex.d 0 1 = 0 := by
    rw [← hg]
    exact hclosed
  have he : Cocycle.fromSingleMk (cochainSourceLiftMorph r t ar 0 (Nat.zero_le r))
      (zero_add 0) 1 rfl hclosed =
      Cocycle.fromSingleMk
        (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0)
        (zero_add 0) 1 rfl hgc := by
    ext : 1
    exact congrArg (fun z => Cochain.fromSingleMk z (zero_add 0)) hg
  unfold cochainSourceLiftClass
  erw [he]
  exact injectiveCochainClass_zero I g hgc

end LinearStudy
