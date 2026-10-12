module
public import Linear.AffineQuasicoherentSourceMorphisms
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
variable {R : CommRingCat.{u}} (M N : (Spec R).Modules) [M.IsQuasicoherent]
/-- The actual affine extension has exactly the supplied global linear
map. This is derived from the existing tilde adjunction, not an input
agreement certificate. No quasicoherence of the target is required. -/
theorem affineQuasicoherentSourceMorphismsEquiv_symm_map
    (f : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    moduleSpecΓFunctor.map ((affineQuasicoherentSourceMorphismsEquiv M N).symm f) = f := by
  exact (affineQuasicoherentSourceMorphismsEquiv_apply M N
    ((affineQuasicoherentSourceMorphismsEquiv M N).symm f)).symm.trans
      ((affineQuasicoherentSourceMorphismsEquiv M N).apply_symm_apply f)
end LinearStudy
