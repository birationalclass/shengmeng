module
public import Linear.SchemePushforwardSourceModuleSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 160000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}
variable (f : X ⟶ Y) (j : Spec R ⟶ Y) [IsOpenImmersion j]

/-- Actual source pushforward of O_X is the unit over f_*O_X. -/
def schemePushforwardStructureSourceUnitIso :
    schemePushforwardSourceModuleSheaf f (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf) := by
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _))

theorem schemePushforwardSourceModuleChart_isQuasicoherent
    (M : X.Modules) [(((Scheme.Modules.pushforward f).obj M).restrict j).IsQuasicoherent] :
    ((show Y.Modules from (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardSourceModuleSheaf f M)).restrict j).IsQuasicoherent := by
  let e := (Scheme.Modules.restrictFunctor j).mapIso
    (schemePushforwardSourceModuleSheaf_scalarRecoveryIso f M)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e.symm inferInstance

theorem schemePushforwardSourceUnitChart_isQuasicoherent
    [(((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).restrict j).IsQuasicoherent] :
    ((show Y.Modules from (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (SheafOfModules.unit ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf))).restrict j).IsQuasicoherent := by
  let e := (Scheme.Modules.restrictFunctor j).mapIso
    ((SheafOfModules.restrictScalars f.toRingCatSheafHom).mapIso
      (schemePushforwardStructureSourceUnitIso f).symm ≪≫
        schemePushforwardSourceModuleSheaf_scalarRecoveryIso f
          (SheafOfModules.unit X.ringCatSheaf))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e.symm inferInstance
end LinearStudy
