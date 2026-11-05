module
public import Linear.NoetherianAffineSchemeActualCohomology
public import Linear.SchemeModuleOpenRestrictionActualAbelian
public import Mathlib.AlgebraicGeometry.Noetherian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
/-- ACTUAL restriction of the underlying sheaf of an arbitrary QC module to EVERY
original affine open of a locally Noetherian scheme has zero positive native H.
No local vanishing certificate is supplied. -/
theorem noetherianAffineOpen_quasicoherent_actualHigherH_vanish
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((topOpenAbelianSheafRestriction X U).obj ((schemeModuleToActualAbelianSheaf X).obj M)) (n+1)) := by
  letI : IsAffine (U : Scheme) := hU
  letI : IsNoetherianRing Γ((U : Scheme),⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤,isAffineOpen_top (U : Scheme)⟩
  let N := M.restrict U.ι
  let H := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (U : Scheme)) (n+1)
  let e := H.mapIso ((schemeModuleOpenRestrictionActualAbelianIso X U).app M)
  letI : Subsingleton (H.obj
      ((Scheme.Modules.restrictFunctor U.ι ⋙ schemeModuleToActualAbelianSheaf U).obj M)) := by
    change Subsingleton (schemeModuleActualCohomology U (M.restrict U.ι) (n+1))
    exact noetherianAffineScheme_quasicoherent_actualHigherH_vanish U (M.restrict U.ι) n
  exact ((AddCommGrpCat.mono_iff_injective e.inv).mp inferInstance).subsingleton
end LinearStudy
