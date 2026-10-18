module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- The ORIGINAL quasicoherent coefficient restricted to an actual affine open has a CONSTRUCTED tilde frame,using native tilde-Gamma adjunction and proved quasicoherence under open restriction. No coefficient frame is assumed. -/
def schemeModuleOpenQuasicoherentCoefficientIso (R : CommRingCat.{u})
    {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    (N : X.Modules) [N.IsQuasicoherent] :
    N.restrict j ≅ tilde ((moduleSpecΓFunctor (R := R)).obj (N.restrict j)) :=
  (asIso (Scheme.Modules.fromTildeΓ (N.restrict j))).symm
end LinearStudy
