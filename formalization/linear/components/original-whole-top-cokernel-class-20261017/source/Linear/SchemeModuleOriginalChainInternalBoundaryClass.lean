module
public import Linear.SchemeModuleCochainResolutionInternalBoundaryClass
public import Linear.OriginalChainIteratedSourceBoundary
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
/-- In EVERY original positive rank,the SAME actual original chain class maps to SAME sheaf-Ext iterated boundary,without assuming desired square,class identity or source projectivity. -/
theorem schemeModuleOriginalChainTopExtClass_internalBoundary
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleGlobalToInternalExtAll
        ((originalChainAsCochain C).opcycles (cochainSourceDegree r r)) N r
      ((Ext.mk₀ (cochainSourceTerminalMap r
        (cochainAugmentationOpcycle (originalChainAugmentationAsCochain C alpha)))).comp
          (originalChainTopExtClass C r alpha a ha) (zero_add r)) =
      schemeModuleHomToInternalExtZero
          ((originalChainAsCochain C).opcycles (cochainSourceDegree r 0)) N
        (originalChainTopOpcycleFunctional C r a ha) ≫
          schemeModuleCochainIteratedInternalBoundary (originalChainAsCochain C) N r
            (originalChainAugmentationAsCochain C alpha) r le_rfl := by
  letI := HasDerivedCategory.standard X.Modules
  haveI : (originalChainAsCochain C).IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (C.extend ComplexShape.embeddingDownNat) 0)
  simpa only [originalChainTopOpcycleFunctional,originalChainTopExtClass] using
    schemeModuleCochainResolutionTopExtClass_internalBoundary (originalChainAsCochain C) r hr
      (originalChainAugmentationAsCochain C alpha)
      ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a)
      (originalChainTopFunctionalCochain_closed C r a ha)
end LinearStudy
