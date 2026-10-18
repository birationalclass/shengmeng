module
public import Linear.SchemeModuleGlobalToInternalExtSourceIso
public import Linear.SchemeModuleOriginalSmallClassBoundary
public import Linear.OriginalChainTerminalSourceIso
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
/-- The ACTUAL image of SAME original small Ext class,with original E target retained. The canonical quotient identification is DERIVED from alpha,not supplied. -/
theorem schemeModuleOriginalSmallClass_internalImage
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleGlobalToInternalExtAll E N r
        (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) =
      schemeModuleHomToInternalExtZero
          ((originalChainAsCochain C).opcycles (cochainSourceDegree r 0)) N
          (originalChainTopOpcycleFunctional C r a ha) ≫
        schemeModuleCochainIteratedInternalBoundary (originalChainAsCochain C) N r
          (originalChainAugmentationAsCochain C alpha) r le_rfl ≫
        schemeModuleInternalExtSourceMap (originalChainTerminalSourceIso C r alpha hAlpha).inv N r := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  have h := schemeModuleGlobalToInternalExtAll_sourceIso
    (originalChainTerminalSourceIso C r alpha hAlpha) N r
    (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha)
  change schemeModuleGlobalToInternalExtAll E N r
      (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) =
    schemeModuleGlobalToInternalExtAll
        ((originalChainAsCochain C).opcycles (cochainSourceDegree r r)) N r
      ((Ext.mk₀ (originalChainTerminalSourceIso C r alpha hAlpha).hom).comp
          (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) (zero_add r)) ≫
      schemeModuleInternalExtSourceMap (originalChainTerminalSourceIso C r alpha hAlpha).inv N r at h
  rw [originalChainTerminalSourceIso_hom,
    schemeModuleOriginalSmallClass_internalBoundary C r hr alpha hAlpha a ha] at h
  simpa only [Category.assoc] using h
end LinearStudy
