module
public import Linear.SchemeModuleOriginalOpcycleExtIndex
public import Linear.CochainOpcycleIteratedBoundary
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
/-- SAME actual quotient/source-Ext comparison in every USED degree,extended by zero only outside n<=r for native sequence naturality. -/
def schemeModuleOriginalOpcycleExtComparison (C : ChainComplex X.Modules ℕ)
    (N : X.Modules) (r n : ℕ) :
    schemeModuleInternalExt (C.opcycles (r-n)) N n ⟶
      schemeModuleInternalExt ((originalChainAsCochain C).opcycles (cochainSourceDegree r n)) N n :=
  if hn : n ≤ r then
    schemeModuleInternalExtSourceMap
      (originalChainAsCochainOpcyclesIso C (cochainSourceDegree r n) (r-n)
        (by rw [cochainSourceDegree_eq]; omega)).hom N n
  else 0
/-- In USED degree the comparison is the native original quotient/source map. -/
theorem schemeModuleOriginalOpcycleExtComparison_eq (C : ChainComplex X.Modules ℕ)
    (N : X.Modules) (r n : ℕ) (hn : n ≤ r) :
    schemeModuleOriginalOpcycleExtComparison C N r n =
      schemeModuleInternalExtSourceMap
        (originalChainAsCochainOpcyclesIso C (cochainSourceDegree r n) (r-n)
          (by rw [cochainSourceDegree_eq]; omega)).hom N n := by
  rw [schemeModuleOriginalOpcycleExtComparison,dif_pos hn]
end LinearStudy
