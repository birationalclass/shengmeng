module
public import Linear.SchemeModuleOriginalBoundarySequenceComparison
public import Linear.SchemeModuleOriginalTopInitialClassEmbedding
public import Linear.SchemeModuleOriginalSmallClassInternalImage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] originalChainAugmentationAsCochain_quasiIso
universe u
variable {X : Scheme.{u}}
/-- Exact SAME original initial Hom class under the finite sequence comparison. -/
theorem schemeModuleOriginalInitialClass_comparison
    (C : ChainComplex X.Modules ℕ) {N : X.Modules} (r : ℕ)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleHomToInternalExtZero (C.opcycles r) N (C.descOpcycles a (r+1) (by simp) ha) ≫
      schemeModuleOriginalOpcycleExtComparison C N r 0 =
      schemeModuleHomToInternalExtZero
          ((originalChainAsCochain C).opcycles (cochainSourceDegree r 0)) N
        (originalChainTopOpcycleFunctional C r a ha) := by
  letI := HasDerivedCategory.standard X.Modules
  rw [schemeModuleOriginalOpcycleExtComparison_eq C N r 0 (Nat.zero_le r)]
  exact (schemeModuleOriginalTopInitialClass_embedding C r a ha).symm
/-- SAME original small Ext class at ACTUAL target E is computed by FULL original Nat-chain source-boundary iteration,with actual endpoints retained. No desired full-iteration identity is supplied. -/
theorem schemeModuleOriginalSmallClass_nativeIterationImage
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleGlobalToInternalExtAll E N r
        (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) =
      schemeModuleHomToInternalExtZero (C.opcycles r) N (C.descOpcycles a (r+1) (by simp) ha) ≫
        schemeModuleOriginalNatIteratedBoundary C N r alpha hAlpha r ≫
        schemeModuleOriginalOpcycleExtComparison C N r r ≫
        schemeModuleInternalExtSourceMap (originalChainTerminalSourceIso C r alpha hAlpha).inv N r := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  rw [schemeModuleOriginalSmallClass_internalImage C r hr alpha hAlpha a ha,
    ← schemeModuleOriginalInitialClass_comparison C r a ha]
  have h := schemeModuleOriginalBoundaryIteration_naturality C N r alpha hAlpha r le_rfl
  have hc := congrArg (fun z =>
    schemeModuleHomToInternalExtZero (C.opcycles r) N
        (C.descOpcycles a (r+1) (by simp) ha) ≫ z ≫
      schemeModuleInternalExtSourceMap (originalChainTerminalSourceIso C r alpha hAlpha).inv N r) h
  simpa only [Category.assoc] using hc.symm
end LinearStudy
