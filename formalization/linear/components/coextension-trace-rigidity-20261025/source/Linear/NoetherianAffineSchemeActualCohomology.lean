module
public import Linear.SchemeModuleSchemeIsoGlobalExt
public import Linear.NoetherianAffineQuasicoherentCohomology
public import Mathlib.AlgebraicGeometry.AffineScheme
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- EVERY arbitrary original affine scheme with Noetherian global ring and EVERY
quasi-coherent original module has zero positive native SHEAF H. Transport uses the
ACTUAL native X.isoSpec and native restriction;no cohomology-vanishing premise. -/
theorem noetherianAffineScheme_quasicoherent_actualHigherH_vanish
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X,⊤)]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (schemeModuleActualCohomology X M (n+1)) := by
  let R := Γ(X,⊤)
  let e : X ≅ Spec R := X.isoSpec
  let N := M.restrict e.inv
  letI : N.IsQuasicoherent := inferInstance
  letI := noetherian_affine_quasicoherent_globalUnitExt_vanish R N n
  let c := schemeModuleSchemeIsoGlobalExtAddEquiv e M (n+1)
  letI : Subsingleton (Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M (n+1)) :=
    c.injective.subsingleton
  exact (schemeModuleGlobalExtActualHAddEquiv X M (n+1)).symm.injective.subsingleton
end LinearStudy
