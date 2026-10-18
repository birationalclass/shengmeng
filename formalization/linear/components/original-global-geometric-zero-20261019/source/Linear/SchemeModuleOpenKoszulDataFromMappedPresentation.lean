module
public import Linear.SchemeModuleOpenKoszulChartData
public import Linear.MappedChainPresentationData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
/-- Reuse the ACTUAL mapped-presentation chain iso and its source. Only the
actual target-complex equality is required, not any Ext or class formula. -/
def schemeModuleOpenKoszulChartData_of_mappedPresentation
    (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {r : ℕ} (H : Fin r → R)
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (hD : d.2.1 = tildeFunctionKoszulComplex R H) :
    schemeModuleOpenKoszulChartData d.1 r :=
  ⟨R,j,inferInstance,H,d.2.2.1 ≪≫ eqToIso hD⟩
end LinearStudy

