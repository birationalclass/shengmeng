module
public import Linear.AcyclicChainHomExtension
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
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- ANY actual positive-exact chain with termwise Ext-acyclicity and positive-exact
ACTUAL Hom cochains has ALL positive Ext from its actual successive opcycles zero.
No boundedness,source projectivity,coefficient injectivity or desired Ext comparison. -/
theorem acyclicChainOpcycle_ext_subsingleton (K : ChainComplex A ℕ) (F : A)
    (hK : ∀ p, K.ExactAt (p+1))
    (hH : ∀ p, (chainActualHomCochain K F).ExactAt (p+1))
    (hA : ∀ p j, Subsingleton (Ext (K.X p) F (j+1)))
    (p n : ℕ) : Subsingleton (Ext (K.opcycles p) F (n+1)) := by
  induction n generalizing p with
  | zero =>
    let S := chainOpcycleSequence K p
    have hS : S.ShortExact := chainOpcycleSequence_shortExact K p (hK p)
    letI : Subsingleton (Ext S.X₂ F 1) := hA p 0
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₃ hS F x
      (Subsingleton.elim _ _) (n₀ := 0) rfl
    obtain ⟨b,hb⟩ := chainActualHomExact_opcycle_extension K F p (hH p) (Ext.homEquiv₀ z)
    let b' : S.X₂ ⟶ F := b
    have hb' : S.f ≫ b' = Ext.homEquiv₀ z := hb
    have hz0 : hS.extClass.comp z (show 1+0=1 from rfl) = 0 := by
      calc
        hS.extClass.comp z (show 1+0=1 from rfl) =
            hS.extClass.comp (Ext.mk₀ (S.f ≫ b')) (show 1+0=1 from rfl) := by
          rw [hb',Ext.mk₀_homEquiv₀_apply]
        _ = hS.extClass.comp ((Ext.mk₀ S.f).comp (Ext.mk₀ b') (zero_add 0)) rfl := by
          rw [Ext.mk₀_comp_mk₀]
        _ = 0 := hS.extClass_comp_assoc (Ext.mk₀ b')
    exact hz.symm.trans hz0
  | succ n ih =>
    let S := chainOpcycleSequence K p
    have hS : S.ShortExact := chainOpcycleSequence_shortExact K p (hK p)
    letI : Subsingleton (Ext S.X₂ F (n+1+1)) := hA p (n+1)
    letI : Subsingleton (Ext S.X₁ F (n+1)) := ih (p+1)
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₃ hS F x
      (Subsingleton.elim _ _) (n₀ := n+1) (by omega)
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0,Ext.comp_zero] at hz
    exact hz.symm
end LinearStudy
