module
public import Linear.OriginalChainTopOpcycleEmbedding
public import Linear.SchemeModuleHomZeroSourceNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- SAME original initial Hom class under the actual comparison is the ACTUAL original chain quotient class,with SAME native source isomorphism. -/
theorem schemeModuleOriginalTopInitialClass_embedding
    (C : ChainComplex X.Modules ℕ) {N : X.Modules}
    (r : ℕ) (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleHomToInternalExtZero
        ((originalChainAsCochain C).opcycles (cochainSourceDegree r 0)) N
        (originalChainTopOpcycleFunctional C r a ha) =
      schemeModuleHomToInternalExtZero (C.opcycles r) N (C.descOpcycles a (r+1) (by simp) ha) ≫
        schemeModuleInternalExtSourceMap (originalChainAsCochainOpcyclesIso C (-(r : ℤ)) r rfl).hom N 0 := by
  letI := HasDerivedCategory.standard X.Modules
  rw [originalChainTopOpcycleFunctional_embedding]
  exact schemeModuleHomToInternalExtZero_sourceNaturality _ _
end LinearStudy
