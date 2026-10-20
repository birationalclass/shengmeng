module
public import Linear.OriginalProjectiveStructureTwistSerre
public import Linear.ProjectivePulledOriginalCovariantSerreBound
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
/-- The proved actual original-V unit-Ext bound discharges the PRECISE
previously isolated geometric Serre statement.No additional premise. -/
theorem originalProjectiveStructureTwist_globalUnitExtSerreBoundStatement {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    ∃ N : ℕ,0 < N ∧ projectivePulledOriginalStructureTwistSerreBoundStatement V N :=
  originalProjectiveStructureTwist_globalUnitExtSerreBound V
end LinearStudy
