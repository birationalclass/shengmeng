module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] [HasExt.{w} A]
/-- Dimension shifting for a class closed under injective quotients,with actual Hom lifting. -/
theorem ext_subsingleton_of_injective_closed_class (O : A) (P : A → Prop)
    (hquot : ∀ {S : ShortComplex A}, S.ShortExact → P S.X₁ → Injective S.X₂ → P S.X₃)
    (hlift : ∀ {S : ShortComplex A}, S.ShortExact → P S.X₁ →
      ∀ f : O ⟶ S.X₃, ∃ g : O ⟶ S.X₂, g ≫ S.g = f)
    (F : A) (hF : P F) (n : ℕ) : Subsingleton (Ext O F (n+1)) := by
  induction n generalizing F with
  | zero =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    letI : Mono S.f := (inferInstance : Mono (Injective.ι F))
    letI : Injective S.X₂ := (inferInstance : Injective (Injective.under F))
    have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (Injective.ι F)⟩
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₁ O hS x
      (Ext.eq_zero_of_injective _) (show 0+1=1 from rfl)
    obtain ⟨t,ht⟩ := hlift hS hF (Ext.homEquiv₀ z)
    have hz0 : z.comp hS.extClass (zero_add 1) = 0 := by
      calc
        z.comp hS.extClass (zero_add 1) =
            (Ext.mk₀ (t ≫ S.g)).comp hS.extClass (zero_add 1) := by
          rw [ht,Ext.mk₀_homEquiv₀_apply]
        _ = 0 := by
          rw [← Ext.mk₀_comp_mk₀_assoc,hS.comp_extClass,Ext.comp_zero]
    exact hz.symm.trans hz0
  | succ n ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    letI : Mono S.f := (inferInstance : Mono (Injective.ι F))
    letI : Injective S.X₂ := (inferInstance : Injective (Injective.under F))
    have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (Injective.ι F)⟩
    have hI : Injective S.X₂ := inferInstance
    letI : Subsingleton (Ext O S.X₃ (n+1)) := ih S.X₃ (hquot hS hF hI)
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₁ O hS x
      (Ext.eq_zero_of_injective _) (show (n+1)+1=n+1+1 from rfl)
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0,Ext.zero_comp] at hz
    exact hz.symm
end LinearStudy
