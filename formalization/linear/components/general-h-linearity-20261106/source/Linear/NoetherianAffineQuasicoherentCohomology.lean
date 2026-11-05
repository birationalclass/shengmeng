module
public import Linear.NoetherianAffineActualCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
universe u
/-- EVERY actual quasi-coherent module sheaf on Noetherian Spec R has zero native derived
SHEAF cohomology in ALL positive degrees. The native tilde/Gamma counit transports the
proved associated-sheaf result to the SAME original sheaf;no acyclicity premise is supplied. -/
theorem noetherian_affine_quasicoherent_actualHigherCohomology_vanish
    (R : CommRingCat.{u}) [IsNoetherianRing R] (M : (Spec R).Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (schemeModuleActualCohomology (Spec R) M (n+1)) := by
  let N : ModuleCat.{u} R := moduleSpecΓFunctor.obj M
  let e : tilde N ≅ M := asIso M.fromTildeΓ
  let F := schemeModuleToActualAbelianSheaf (Spec R)
  let H : TopCat.Sheaf AddCommGrpCat.{u} (Spec R) ⥤ AddCommGrpCat.{u} :=
    CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (Spec R)) (n+1)
  let h := H.mapIso (F.mapIso e)
  letI : Subsingleton (H.obj (F.obj (tilde N))) :=
    noetherian_affine_tilde_actualHigherCohomology_vanish R N n
  exact ((AddCommGrpCat.mono_iff_injective h.inv).mp inferInstance).subsingleton

/-- The SAME arbitrary quasi-coherent sheaf has zero positive GLOBAL structure-unit Ext,
via the previously verified canonical comparison with actual native SHEAF H. -/
theorem noetherian_affine_quasicoherent_globalUnitExt_vanish
    (R : CommRingCat.{u}) [IsNoetherianRing R] (M : (Spec R).Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Ext.{u} (SheafOfModules.unit (Spec R).ringCatSheaf) M (n+1)) := by
  letI := noetherian_affine_quasicoherent_actualHigherCohomology_vanish R M n
  exact (schemeModuleGlobalExtActualHAddEquiv (Spec R) M (n+1)).injective.subsingleton
end LinearStudy