module
public import Linear.OriginalGlobalModuleScalar
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}}

/-- Tilde carries module scalar multiplication to multiplication by the
actual original global structure-sheaf section, on the same sheaf. -/
theorem originalTildeScalar (c : R) (M : ModuleCat R) :
    (tilde.functor R).map (ModuleCat.ofHom (c • (LinearMap.id : M →ₗ[R] M))) =
      originalGlobalModuleScalar ((Scheme.ΓSpecIso R).inv c) (tilde M) := by
  apply (modulesSpecToSheaf (R := R)).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  change ((tilde.modulesSpecToSheafIso M).app U).inv
      (StructureSheaf.comapₗ (c • (LinearMap.id : M →ₗ[R] M)) U.unop U.unop .rfl
        (((tilde.modulesSpecToSheafIso M).app U).hom x)) =
      c • (show Γ(tilde M,U.unop) from x)
  have hc : StructureSheaf.comapₗ (c • (LinearMap.id : M →ₗ[R] M))
      U.unop U.unop .rfl (((tilde.modulesSpecToSheafIso M).app U).hom x) =
      c • (((tilde.modulesSpecToSheafIso M).app U).hom x) := by
    apply Subtype.ext
    funext y
    change StructureSheaf.Localizations.comapFun (c • (LinearMap.id : M →ₗ[R] M)) y.1
      ((((tilde.modulesSpecToSheafIso M).app U).hom x).val y) =
      c • ((((tilde.modulesSpecToSheafIso M).app U).hom x).val y)
    induction ((tilde.modulesSpecToSheafIso M).app U).hom x |>.val y
        using LocalizedModule.induction_on with
    | h a b =>
      rw [LocalizedModule.smul'_mk]
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, RingHom.id_apply] using
        StructureSheaf.Localizations.comapFun_mk
          (c • (LinearMap.id : M →ₗ[R] M)) y.1 a b
  rw [hc]
  exact (((tilde.modulesSpecToSheafIso M).app U).inv.hom.map_smul c _).trans
    (congrArg (c • ·) (((tilde.modulesSpecToSheafIso M).app U).hom_inv_id_apply x))

/-- The actual structure sheaf comparison retains its specified maps;
conjugated affine multiplication is the global structure-sheaf scalar. -/
theorem originalTildeScalar_unit (c : R) :
    let t : tilde (ModuleCat.of R R) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf := tildeSelf
    t.inv ≫ (tilde.functor R).map
      (ModuleCat.ofHom (c • (LinearMap.id : R →ₗ[R] R))) ≫ t.hom =
      originalGlobalModuleScalar ((Scheme.ΓSpecIso R).inv c)
        (SheafOfModules.unit (Spec R).ringCatSheaf) := by
  change 𝟙 _ ≫ (tilde.functor R).map
    (ModuleCat.ofHom (c • (LinearMap.id : R →ₗ[R] R))) ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp]
  exact originalTildeScalar c (ModuleCat.of R R)

end LinearStudy
