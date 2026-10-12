module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 160000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (S : TopCat.Sheaf RingCat Y)
variable (α : Y.ringCatSheaf ⟶ S) (j : X ⟶ Y) [IsOpenImmersion j]

/-- Restrict the ACTUAL source-ring sheaf along the original open chart.
Its sections over W are the original source functions over j(W). -/
def schemeSourceRingChartRestriction : TopCat.Sheaf RingCat X :=
  (j.opensFunctor.sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj S

/-- The base-ring map on the actual source-ring restriction is obtained
from the original chart appIso and the original base-ring map. -/
def schemeSourceRingChartRestrictionBaseMap :
    X.ringCatSheaf ⟶ schemeSourceRingChartRestriction S j := by
  let β : X.presheaf ⟶ j.opensFunctor.op ⋙ Y.presheaf :=
    { app W := (j.appIso W.unop).inv }
  exact ⟨Functor.whiskerRight β (forget₂ CommRingCat RingCat) ≫
    Functor.whiskerLeft j.opensFunctor.op α.hom⟩

/-- Restrict the SAME actual source module, retaining all sections,
restrictions and source multiplication. -/
def schemeSourceModuleChartRestriction (M : SheafOfModules.{u} S) :
    SheafOfModules (schemeSourceRingChartRestriction S j) :=
  (SheafOfModules.pushforward (F := j.opensFunctor)
    (𝟙 (schemeSourceRingChartRestriction S j))).obj M

/-- Base scalar restriction recovers the ORIGINAL chart restriction
of the original base module, with the identity on every section. -/
def schemeSourceModuleChartRestriction_scalarRecoveryIso (M : SheafOfModules.{u} S) :
    (SheafOfModules.restrictScalars (schemeSourceRingChartRestrictionBaseMap S α j)).obj
      (schemeSourceModuleChartRestriction S j M) ≅
    ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M).restrict j) := by
  exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _))

theorem schemeSourceModuleChartRestriction_scalarRecoveryIso_hom_apply
    (M : SheafOfModules.{u} S) (W : X.Opens)
    (x : Γ((show X.Modules from
      (SheafOfModules.restrictScalars (schemeSourceRingChartRestrictionBaseMap S α j)).obj
        (schemeSourceModuleChartRestriction S j M)),W)) :
    (schemeSourceModuleChartRestriction_scalarRecoveryIso S α j M).hom.val.app (op W) x =
      (show Γ(((show Y.Modules from (SheafOfModules.restrictScalars α).obj M).restrict j),W)
        from x) := rfl
end LinearStudy
