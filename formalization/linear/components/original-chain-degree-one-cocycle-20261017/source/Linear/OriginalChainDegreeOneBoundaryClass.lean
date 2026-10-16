module
public import Linear.OriginalChainDegreeOneRoofClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- The SAME original degree-one class with ANY top functional is the native
contravariant zero boundary. Both native MINUS signs have been retained. -/
theorem originalChainDegreeOneTopExtClass_eq_boundary
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0)
    (he : ∀ p : ℕ,0 < p → C.ExactAt p) {N : A} (a : C.X 1 ⟶ N) :
    letI := originalChainCokernelAugmentation_quasiIso C he
    originalChainTopExtClass C 1 (originalChainCokernelAugmentation C)
      a (by simp [h]) =
      Ext.δ (originalChainFirstCokernelSequence_shortExact C h (he 1 (by omega)))
        0 1 rfl (Ext.mk₀ a) := by
  letI := originalChainCokernelAugmentation_quasiIso C he
  have hc := originalChainTopExtClass_comp_mk₀ C 1 (originalChainCokernelAugmentation C)
    (𝟙 (C.X 1)) (by simp [h]) a
  simp only [Category.id_comp] at hc
  rw [originalChainDegreeOneTopExtClass_eq_neg_roof C h he,Ext.neg_comp] at hc
  rw [cochainShortExactRoofClass_contravariant_zero_sign]
  exact hc.symm

end LinearStudy
