module
public import Linear.CochainOpcycleSignedExtension
public import Linear.CochainResolutionIteratedSourceBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]
/-- The SAME actual top quotient projection descends to the identity on
the SAME actual opcycles. Native cokernel universality proves it. -/
theorem cochainTopOpcycleFunctional_projection
    (K : CochainComplex A ℤ) (r : ℕ) :
    cochainTopOpcycleFunctional K r (K.pOpcycles (-(r : ℤ)))
      (K.d_pOpcycles (-(r : ℤ)-1) (-(r : ℤ))) =
      𝟙 (K.opcycles (-(r : ℤ))) := by
  apply (cancel_epi (K.pOpcycles (-(r : ℤ)))).mp
  simp only [cochainTopOpcycleFunctional,HomologicalComplex.p_descOpcycles,Category.comp_id]
/-- The ACTUAL native signed extension is the SAME original resolution
roof class of the actual top quotient projection,under the constructed
terminal augmentation. No class comparison or cohomology input. -/
theorem cochainOpcycleSignedExtension_eq_actual_roof
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E : A} (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (I : InjectiveResolution (K.opcycles (cochainSourceDegree r 0))) :
    cochainOpcycleSignedExtension K r alpha r le_rfl =
      (Ext.mk₀ (cochainSourceTerminalMap r (cochainAugmentationOpcycle alpha))).comp
        (cochainResolutionTopExtClass K r alpha (K.pOpcycles (-(r : ℤ)))
          (K.d_pOpcycles (-(r : ℤ)-1) (-(r : ℤ)))) (zero_add r) := by
  simpa only [cochainTopOpcycleFunctional_projection,cochainOpcycleSignedExtension,cochainSourceDegree] using
    cochainResolutionTopExtClass_iteratedSourceBoundary K r hr alpha
      (K.pOpcycles (-(r : ℤ))) (K.d_pOpcycles (-(r : ℤ)-1) (-(r : ℤ))) I
end LinearStudy
