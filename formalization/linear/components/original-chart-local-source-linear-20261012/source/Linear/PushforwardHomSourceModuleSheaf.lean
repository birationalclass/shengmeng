module
public import Linear.PushforwardHomSourceActionModule
public import Mathlib.Topology.Sheaves.Functors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

/-- The original internal Hom is an actual module SHEAF over f_*O_X.
Its section carrier and restriction maps are unchanged; the source action
and its restriction compatibility have already been proved. -/
def schemePushforwardHomSourceModuleSheaf (f : X ⟶ Y) (N : Y.Modules) :
    SheafOfModules ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf) := by
  let P := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let H := schemeModuleHomModuleSheaf P N
  let R := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
  letI (U : Y.Opensᵒᵖ) : SMul (R.obj.obj U) (H.presheaf.obj U) :=
    ⟨schemePushforwardHomSourceActionSection f N U.unop⟩
  letI (U : Y.Opensᵒᵖ) : Module (R.obj.obj U) (H.presheaf.obj U) :=
    schemePushforwardHomSourceModule f N U.unop
  refine { val := PresheafOfModules.ofPresheaf (R := R.obj) H.presheaf ?_,
           isSheaf := H.isSheaf }
  intro U V i b h
  exact schemePushforwardHomSourceActionSection_restrict f N i.unop b h

/-- The global source-module construction uses the SAME original Hom
presheaf: no replacement carrier, restriction, or sheafification is inserted. -/
theorem schemePushforwardHomSourceModuleSheaf_original_presheaf
    (f : X ⟶ Y) (N : Y.Modules) :
    (schemePushforwardHomSourceModuleSheaf f N).val.presheaf =
    (schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).presheaf := rfl

end LinearStudy
