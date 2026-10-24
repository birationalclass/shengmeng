module
public import Linear.SchemeModuleOpenKoszulChartData
public import Linear.SchemeModuleRestrictionUnitHEq
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- Statement only for arbitrary ACTUAL chart data and ACTUAL target. -/
def schemeModuleChartInternalExtSupportStatement {X : Scheme.{u}}
    (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (D : schemeModuleOpenKoszulChartData C r) (E : X.Modules) : Prop :=
  letI := D.2.2.1
  ∀ N q,IsIso ((Scheme.Modules.restrictAdjunction D.2.1).unit.app
    (schemeModuleInternalExt E N q))
/-- Package the entire all-coefficient/all-degree support law GENERICALLY
along proved chart-object equalities. Concrete original applications
keep this type opaque rather than rechecking the dependent package. -/
theorem schemeModuleChartInternalExtSupportStatement_of_chartHEq
    {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (D : schemeModuleOpenKoszulChartData C r) (E : X.Modules)
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (hR : D.1 = R) (hj : HEq D.2.1 j)
    (hU : ∀ N q,IsIso ((Scheme.Modules.restrictAdjunction j).unit.app
      (schemeModuleInternalExt E N q))) :
    schemeModuleChartInternalExtSupportStatement C r D E := by
  letI := D.2.2.1
  intro N q
  exact schemeModule_restrictionUnit_isIso_of_chartHEq D.2.1 j hR hj
    (schemeModuleInternalExt E N q) (hU N q)
end LinearStudy
