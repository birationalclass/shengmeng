module
public import Linear.OriginalChainOpcycleIndex
public import Linear.SchemeModuleInternalExtSourceMap
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
/-- Explicit source-index transport preserves SAME actual derived-sheaf-Ext source map of the original quotient iso. -/
theorem schemeModuleOriginalOpcycleExtSourceMap_index (C : ChainComplex X.Modules ℕ)
    (N : X.Modules) (q : ℕ) (j : ℤ) (n m : ℕ)
    (hn : -(n : ℤ)=j) (hm : -(m : ℤ)=j) (h : n=m) :
    eqToHom (congrArg (fun z => schemeModuleInternalExt (C.opcycles z) N q) h) ≫
      schemeModuleInternalExtSourceMap (originalChainAsCochainOpcyclesIso C j m hm).hom N q =
        schemeModuleInternalExtSourceMap (originalChainAsCochainOpcyclesIso C j n hn).hom N q := by
  subst m
  simp only [eqToHom_refl,Category.id_comp]
end LinearStudy
