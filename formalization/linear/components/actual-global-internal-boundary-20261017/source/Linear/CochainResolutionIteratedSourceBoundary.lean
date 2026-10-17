module
public import Linear.CochainResolutionSourceBoundaryClass
public import Linear.CochainSourceLiftInitialClass
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

/-- SAME original top functional descends through the native source quotient. -/
def cochainTopOpcycleFunctional (K : CochainComplex A ℤ) {N : A} (r : ℕ)
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0) :
    K.opcycles (cochainSourceDegree r 0) ⟶ N :=
  K.descOpcycles (i := -(r : ℤ)) a (-(r : ℤ)-1) (by simp) ha

/-- SAME original top class is EXACTLY the actual native iterated source
boundary,after the canonical augmentation quotient identification. Construct
all lifts and intermediate classes;no projectivity or desired identity input. -/
theorem cochainResolutionTopExtClass_iteratedSourceBoundary
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0)
    (I : InjectiveResolution N) :
    cochainOpcycleIteratedBoundary K r alpha r le_rfl
      (Ext.mk₀ (cochainTopOpcycleFunctional K r a ha)) =
      (Ext.mk₀ (cochainSourceTerminalMap r (cochainAugmentationOpcycle alpha))).comp
        (cochainResolutionTopExtClass K r alpha a ha) (zero_add r) := by
  obtain ⟨f,hf,t,har,hB,hclass,htop,hend⟩ :=
    cochainResolutionSourceBoundaryClass_exists K r hr alpha a ha I
  let ar := cochainSourceTerminalMorph r (cochainAugmentationOpcycle alpha ≫ f)
  have hg : cochainSourceLiftMorph r t ar 0 (Nat.zero_le r) =
      cochainTopOpcycleFunctional K r a ha ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0 := by
    apply (cancel_epi (K.pOpcycles (-(r : ℤ)))).1
    rw [htop]
    simp only [cochainTopOpcycleFunctional,← Category.assoc,
      HomologicalComplex.p_descOpcycles]
  have hstart := cochainSourceLiftClass_initial I r t ar har hB
    (cochainTopOpcycleFunctional K r a ha) hg
  rw [hstart] at hend
  exact hend

end LinearStudy
