module
public import Linear.OriginalGlobalModuleScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

/-- Restriction of multiplication by the ACTUAL global structure section
is multiplication by its ACTUAL pullback, for the same module. This is
the scalar compatibility needed for original affine Hom chart transport. -/
theorem originalGlobalModuleScalar_restrict (j : X ⟶ Y) [IsOpenImmersion j]
    (r : Γ(Y,⊤)) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor j).map (originalGlobalModuleScalar r M) =
      originalGlobalModuleScalar (j.appTop r) (M.restrict j) := by
  apply SheafOfModules.hom_ext
  ext W x
  let U : X.Opens := W.unop
  change (show Γ(Y,j ''ᵁ U) from Y.presheaf.map (j ''ᵁ U).leTop.op r) •
      (show Γ(M,j ''ᵁ U) from x) =
    (show Γ(Y,j ''ᵁ U) from (j.appIso U).inv
      (X.presheaf.map U.leTop.op (j.appTop r))) •
      (show Γ(M,j ''ᵁ U) from x)
  congr 1
  apply (ConcreteCategory.bijective_of_isIso (j.appIso U).hom).injective
  dsimp only
  rw [Iso.inv_hom_id_apply]
  have he : Y.presheaf.map (j ''ᵁ U).leTop.op ≫ (j.appIso U).hom =
      j.appTop ≫ X.presheaf.map U.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rfl
  exact congr($(he) r)

end LinearStudy
