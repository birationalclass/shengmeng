module
public import Linear.CochainOpcycleSignedExtension
public import Linear.CochainOpcycleUnsignedExact
public import Linear.ExtUnitSmulComposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- ACTUAL native signed connecting map is onto under explicit relative
Ext vanishings of SAME original terms. The sign comparison is proved. -/
theorem cochainOpcycleSignedExtension_surjective
    (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree r j+1)) q)) :
    ∀ x : Ext O (K.opcycles (cochainSourceDegree r 0)) r,
      ∃ y : Ext O (K.opcycles (cochainSourceDegree r r)) 0,
        y.comp (cochainOpcycleSignedExtension K r alpha r le_rfl) (zero_add r) = x := by
  obtain ⟨s,hs⟩ := cochainOpcycleSignedExtension_eq_unit_smul_unsigned K r alpha r le_rfl
  intro x
  obtain ⟨y,hy⟩ := cochainOpcycleUnsignedExtension_surjective K r alpha O hvan (s⁻¹ • x)
  refine ⟨y,?_⟩
  rw [hs,ext_comp_unit_smul,hy,smul_inv_smul]
/-- SAME actual projection gives exactly the kernel of the actual NATIVE
signed connecting map. This is not a freely chosen unsigned substitute. -/
theorem cochainOpcycleSignedExtension_kernel
    (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (O : A) (n : ℕ) (hn : n+1 ≤ r)
    (hvan : ∀ j,j < n → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree r j+1)) q))
    (x : Ext O (K.opcycles (cochainSourceDegree r (n+1))) 0) :
    x.comp (cochainOpcycleSignedExtension K r alpha (n+1) hn) (zero_add _) = 0 ↔
      ∃ y : Ext O (K.X (cochainSourceDegree r n+1)) 0,
        y.comp (Ext.mk₀ (K.pOpcycles (cochainSourceDegree r n+1))) (add_zero _) = x := by
  obtain ⟨s,hs⟩ := cochainOpcycleSignedExtension_eq_unit_smul_unsigned K r alpha (n+1) hn
  rw [hs,ext_comp_unit_smul_zero_iff]
  exact cochainOpcycleUnsignedExtension_kernel K r alpha O n hn hvan x
end LinearStudy
