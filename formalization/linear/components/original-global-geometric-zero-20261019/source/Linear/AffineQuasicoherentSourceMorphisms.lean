module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {R : CommRingCat.{u}} (M N : (Spec R).Modules)
variable [M.IsQuasicoherent]

/-- On the actual affine scheme, a quasicoherent source allows every
R-linear map of global sections to extend uniquely to a module-sheaf
morphism. No quasicoherence of the target is assumed. -/
def affineQuasicoherentSourceMorphismsEquiv :
    (M ⟶ N) ≃ (moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :=
  (Iso.homCongr (asIso M.fromTildeΓ).symm (Iso.refl N)).trans
    ((tilde.adjunction (R := R)).homEquiv (moduleSpecΓFunctor.obj M) N)

/-- This equivalence is exactly the genuine global-sections map, hence
it controls the whole module-sheaf morphism, not only point values. -/
theorem affineQuasicoherentSourceMorphismsEquiv_apply (g : M ⟶ N) :
    affineQuasicoherentSourceMorphismsEquiv M N g = moduleSpecΓFunctor.map g := by
  change (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj M) ≫
    moduleSpecΓFunctor.map (M.fromTildeΓ ≫ g) = moduleSpecΓFunctor.map g
  rw [Functor.map_comp, ← Category.assoc]
  change ((tilde.adjunction (R := R)).unit.app _ ≫
    moduleSpecΓFunctor.map ((tilde.adjunction (R := R)).counit.app M)) ≫
      moduleSpecΓFunctor.map g = moduleSpecΓFunctor.map g
  rw [(tilde.adjunction (R := R)).right_triangle_components]
  rfl
end LinearStudy
