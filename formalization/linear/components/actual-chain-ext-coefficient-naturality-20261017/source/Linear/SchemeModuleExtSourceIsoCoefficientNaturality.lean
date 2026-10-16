module
public import Linear.SchemeModuleAcyclicChainExtIndependence
public import Linear.SchemeModuleIteratedShiftCoefficientNaturality
public import Linear.SchemeModuleOpcycleHomCoefficientNaturality
public import Linear.SchemeModuleTopHomologyCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Fixed ACTUAL source-isomorphism transport is natural in the coefficient sheaf. -/
theorem schemeModuleInternalExtSourceIso_inv_coefficientNaturality
    {P Q : X.Modules} (e : P ≅ Q) {N M : X.Modules} (c : N ⟶ M) (q : ℕ) :
    (schemeModuleInternalExtFunctor Q q).map c ≫ (schemeModuleInternalExtSourceIso e M q).inv =
      (schemeModuleInternalExtSourceIso e N q).inv ≫ (schemeModuleInternalExtFunctor P q).map c :=
  (NatTrans.rightDerived (schemeModuleInternalHomSourceNatTrans e.hom) q).naturality c


end LinearStudy
