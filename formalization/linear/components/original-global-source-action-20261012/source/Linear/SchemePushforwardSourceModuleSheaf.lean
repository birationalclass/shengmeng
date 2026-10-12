module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
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

/-- Actual module pushforward over the actual source-ring pushforward.
The original sections and their original O_X action are retained. -/
def schemePushforwardSourceModuleSheaf (f : X ⟶ Y) (M : X.Modules) :
    SheafOfModules ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf) :=
  (SheafOfModules.pushforward (F := Opens.map f.base)
    (𝟙 ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf))).obj M

theorem schemePushforwardSourceModuleSheaf_original_presheaf
    (f : X ⟶ Y) (M : X.Modules) :
    (schemePushforwardSourceModuleSheaf f M).val.presheaf =
      ((Scheme.Modules.pushforward f).obj M).val.presheaf := rfl

/-- Restricting the actual source ring to O_Y gives the ORIGINAL module
pushforward, with the identity on all original sections. -/
def schemePushforwardSourceModuleSheaf_scalarRecoveryIso
    (f : X ⟶ Y) (M : X.Modules) :
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardSourceModuleSheaf f M) ≅
    (Scheme.Modules.pushforward f).obj M := by
  exact (SheafOfModules.fullyFaithfulForget Y.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))

theorem schemePushforwardSourceModuleSheaf_scalarRecoveryIso_hom_apply
    (f : X ⟶ Y) (M : X.Modules) (U : Y.Opens)
    (x : ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardSourceModuleSheaf f M)).val.obj (op U)) :
    (schemePushforwardSourceModuleSheaf_scalarRecoveryIso f M).hom.val.app (op U) x =
    (show Γ((Scheme.Modules.pushforward f).obj M,U) from x) := rfl

theorem schemePushforwardSourceModuleSheaf_original_source_smul
    (f : X ⟶ Y) (M : X.Modules) (U : Y.Opens)
    (b : ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf).obj.obj (op U))
    (x : (schemePushforwardSourceModuleSheaf f M).val.obj (op U)) :
    b • x = (show Γ(M,f ⁻¹ᵁ U) from (show Γ(X,f ⁻¹ᵁ U) from b) • (show Γ(M,f ⁻¹ᵁ U) from x)) := rfl

end LinearStudy
