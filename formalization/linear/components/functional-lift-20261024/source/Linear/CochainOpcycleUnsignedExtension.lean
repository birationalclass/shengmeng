module
public import Linear.IteratedCovariantExtExact
public import Linear.CochainOpcycleIteratedBoundary
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
/-- Unsigned Yoneda composite of the SAME actual original opcycle source
sequences. All short exactness is DERIVED from actual augmentation alpha.
Its comparison with native signed source boundaries is a separate proof. -/
def cochainOpcycleUnsignedExtension (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n ≤ r) :
    Ext (K.opcycles (cochainSourceDegree r n)) (K.opcycles (cochainSourceDegree r 0)) n :=
  iteratedCovariantExtClass
    (fun j => K.opcycles (cochainSourceDegree r j))
    (fun j => K.X (cochainSourceDegree r j+1))
    (fun j => K.fromOpcycles (cochainSourceDegree r j) (cochainSourceDegree r j+1))
    (fun j => K.pOpcycles (cochainSourceDegree r j+1))
    (fun j => (cochainOpcycleSourceSequence K (cochainSourceDegree r j)).zero)
    r (fun j hj => cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r j)
      (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq];omega))) n hn

theorem cochainOpcycleUnsignedExtension_zero (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha] :
    cochainOpcycleUnsignedExtension K r alpha 0 (Nat.zero_le r) =
      Ext.mk₀ (𝟙 (K.opcycles (cochainSourceDegree r 0))) := rfl

theorem cochainOpcycleUnsignedExtension_succ (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n+1 ≤ r) :
    cochainOpcycleUnsignedExtension K r alpha (n+1) hn =
      (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
        (cochainAugmentation_exactAt_negative K alpha _
          (by rw [cochainSourceDegree_eq];omega))).extClass.comp
        (cochainOpcycleUnsignedExtension K r alpha n (by omega)) (by omega) := rfl
end LinearStudy
