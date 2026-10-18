module
public import Linear.SchemeModuleOpenKoszulDataFromMappedPresentation
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
attribute [local irreducible] CategoryTheory.Functor.mapHomologicalComplex
/-- Transport only the source of the ACTUAL chart iso, retaining the
literal ring,inclusion and equations as fields. No whole Sigma cast. -/
def schemeModuleOpenKoszulChartData_of_sourceIdentification
    (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {r : ℕ} (H : Fin r → R) (C : ChainComplex X.Modules ℕ)
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (hC : d.1 = C) (hD : d.2.1 = tildeFunctionKoszulComplex R H) :
    schemeModuleOpenKoszulChartData C r :=
  ⟨R,j,inferInstance,H,
    eqToIso (congrArg
      (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj)
      hC.symm) ≪≫ d.2.2.1 ≪≫ eqToIso hD⟩
end LinearStudy

