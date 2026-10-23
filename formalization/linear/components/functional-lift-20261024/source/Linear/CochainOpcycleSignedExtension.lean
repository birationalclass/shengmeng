module
public import Linear.CochainOpcycleUnsignedExtension
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
/-- The actual NATIVE signed iterated extension,constructed from the SAME
actual source boundaries and the actual identity. No class law is input. -/
def cochainOpcycleSignedExtension (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n ≤ r) :
    Ext (K.opcycles (cochainSourceDegree r n)) (K.opcycles (cochainSourceDegree r 0)) n :=
  cochainOpcycleIteratedBoundary K r alpha n hn (Ext.mk₀ (𝟙 _))
/-- The two ACTUAL sign conventions differ only by a constructed integer
UNIT. This preserves covariant kernels and surjectivity;neither fact nor
a comparison of independently chosen classes is assumed. -/
theorem cochainOpcycleSignedExtension_eq_unit_smul_unsigned
    (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n ≤ r) :
    ∃ s : ℤˣ,cochainOpcycleSignedExtension K r alpha n hn =
      s • cochainOpcycleUnsignedExtension K r alpha n hn := by
  induction n with
  | zero =>
    refine ⟨1,?_⟩
    simp [cochainOpcycleSignedExtension,cochainOpcycleIteratedBoundary,
      cochainOpcycleUnsignedExtension_zero]
  | succ n ih =>
    obtain ⟨s,hs⟩ := ih (by omega)
    refine ⟨Int.negOnePow (n+1) * s,?_⟩
    change Ext.δ (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
        (cochainAugmentation_exactAt_negative K alpha _
          (by rw [cochainSourceDegree_eq];omega))) n (n+1) rfl
      (cochainOpcycleSignedExtension K r alpha n (by omega)) = _
    rw [Ext.δ_apply,hs]
    let S := cochainOpcycleSourceSequence K (cochainSourceDegree r n)
    have hS : S.ShortExact := cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
      (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq];omega))
    have hlin : hS.extClass.comp
        (s • cochainOpcycleUnsignedExtension K r alpha n (by omega)) (show 1+n=n+1 by omega) =
        s • hS.extClass.comp
          (cochainOpcycleUnsignedExtension K r alpha n (by omega)) (show 1+n=n+1 by omega) := by
      change (hS.extClass.precomp _ (show 1+n=n+1 by omega)) (s • _) =
        s • (hS.extClass.precomp _ (show 1+n=n+1 by omega)) _
      simp only [Units.smul_def,map_zsmul]
    rw [hlin,smul_smul,cochainOpcycleUnsignedExtension_succ]
    simp only [Nat.cast_add,Nat.cast_one]
end LinearStudy
