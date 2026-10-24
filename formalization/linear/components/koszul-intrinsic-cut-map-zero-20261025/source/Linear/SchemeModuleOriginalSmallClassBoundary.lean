module
public import Linear.OriginalChainTopExtUniverse
public import Linear.SchemeModuleOriginalClassGlobalToLocal
public import Linear.SchemeModuleOriginalChainInternalBoundaryClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] originalChainAugmentationAsCochain_quasiIso
universe u
variable {X : Scheme.{u}}
/-- The already constructed ORIGINAL standard class,after native small-Ext transport,is the SAME native roof class. -/
theorem schemeModuleOriginalChainTopExtClassSmall_eq_native
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha =
      (originalChainTopExtClass.{u,u+1,u,u+1} C r alpha a ha : Ext.{u} E N r) := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  letI : HasExt.{u+1} X.Modules := HasExt.standard X.Modules
  exact nativeExtUniverseEquiv_originalChainTopExtClass.{u+1,u,u+1,u,u+1} C r alpha a ha
/-- The SAME ORIGINAL small global Ext class maps to the actual sheaf boundary iteration of the SAME top functional,for EVERY positive original rank. -/
theorem schemeModuleOriginalSmallClass_internalBoundary
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleGlobalToInternalExtAll
        ((originalChainAsCochain C).opcycles (cochainSourceDegree r r)) N r
      ((Ext.mk₀ (cochainSourceTerminalMap r
        (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha)))).comp
          (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) (zero_add r)) =
      schemeModuleHomToInternalExtZero
          ((originalChainAsCochain C).opcycles (cochainSourceDegree r 0)) N
        (originalChainTopOpcycleFunctional C r a ha) ≫
          schemeModuleCochainIteratedInternalBoundary (originalChainAsCochain C) N r
            (originalChainAugmentationAsCochain C alpha) r le_rfl := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  rw [schemeModuleOriginalChainTopExtClassSmall_eq_native]
  exact schemeModuleOriginalChainTopExtClass_internalBoundary C r hr alpha a ha
end LinearStudy
