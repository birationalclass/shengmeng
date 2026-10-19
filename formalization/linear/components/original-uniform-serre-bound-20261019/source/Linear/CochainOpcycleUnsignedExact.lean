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
/-- Actual covariant opcycle boundary is ONTO under explicit positive
cohomological Ext vanishings of the SAME original middle terms. -/
theorem cochainOpcycleUnsignedExtension_surjective
    (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (O : A)
    (hvan : ∀ j,j < r → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree r j+1)) q)) :
    ∀ x : Ext O (K.opcycles (cochainSourceDegree r 0)) r,
      ∃ y : Ext O (K.opcycles (cochainSourceDegree r r)) 0,
        y.comp (cochainOpcycleUnsignedExtension K r alpha r le_rfl) (zero_add r) = x := by
  exact
    iteratedCovariantExtClass_postcomp_surjective
    (fun j => K.opcycles (cochainSourceDegree r j))
    (fun j => K.X (cochainSourceDegree r j+1))
    (fun j => K.fromOpcycles (cochainSourceDegree r j) (cochainSourceDegree r j+1))
    (fun j => K.pOpcycles (cochainSourceDegree r j+1))
    (fun j => (cochainOpcycleSourceSequence K (cochainSourceDegree r j)).zero)
    r (fun j hj => cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r j)
      (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq];omega))) O r le_rfl hvan 0 r (zero_add r)
/-- Actual original middle projection gives EXACTLY the kernel of the
SAME iterated unsigned opcycle boundary. No projectivity is supplied. -/
theorem cochainOpcycleUnsignedExtension_kernel
    (K : CochainComplex A ℤ) {E : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (O : A) (n : ℕ) (hn : n+1 ≤ r)
    (hvan : ∀ j,j < n → ∀ q,0 < q →
      Subsingleton (Ext O (K.X (cochainSourceDegree r j+1)) q))
    (x : Ext O (K.opcycles (cochainSourceDegree r (n+1))) 0) :
    x.comp (cochainOpcycleUnsignedExtension K r alpha (n+1) hn) (zero_add _) = 0 ↔
      ∃ y : Ext O (K.X (cochainSourceDegree r n+1)) 0,
        y.comp (Ext.mk₀ (K.pOpcycles (cochainSourceDegree r n+1))) (add_zero _) = x := by
  exact iteratedCovariantExtClass_kernel
    (fun j => K.opcycles (cochainSourceDegree r j))
    (fun j => K.X (cochainSourceDegree r j+1))
    (fun j => K.fromOpcycles (cochainSourceDegree r j) (cochainSourceDegree r j+1))
    (fun j => K.pOpcycles (cochainSourceDegree r j+1))
    (fun j => (cochainOpcycleSourceSequence K (cochainSourceDegree r j)).zero)
    r (fun j hj => cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r j)
      (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq];omega))) O n hn hvan x
end LinearStudy
