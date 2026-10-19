module
public import Linear.CochainOpcycleIteratedBoundary
public import Linear.SchemeModuleInternalExtSourceBoundaryNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- SAME actual sheaf-Ext boundary for n<r,extended by zero outside the used finite range solely to use native OfSequence.map. -/
def schemeModuleCochainInternalBoundaryStep (K : CochainComplex X.Modules ℤ)
    {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha]
    (n : ℕ) :
    schemeModuleInternalExt (K.opcycles (cochainSourceDegree r n)) N n ⟶
      schemeModuleInternalExt (K.opcycles (cochainSourceDegree r (n+1))) N (n+1) :=
  if hn : n < r then
    schemeModuleInternalExtSourceBoundary (cochainOpcycleSourceSequence K (cochainSourceDegree r n))
      (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
        (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega))) N n
  else 0
/-- In every USED degree the step is EXACTLY the native derived-sheaf-Ext boundary. -/
theorem schemeModuleCochainInternalBoundaryStep_eq (K : CochainComplex X.Modules ℤ)
    {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n < r) :
    schemeModuleCochainInternalBoundaryStep K N r alpha n =
      schemeModuleInternalExtSourceBoundary (cochainOpcycleSourceSequence K (cochainSourceDegree r n))
        (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
          (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega))) N n := by
  rw [schemeModuleCochainInternalBoundaryStep,dif_pos hn]
end LinearStudy
