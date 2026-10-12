module
public import Linear.SchemePushforwardSourceModuleSheaf
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

/-- Actual original source multiplication on the SAME original
base pushforward sections. It is not an arbitrary module action. -/
def schemePushforwardOriginalSourceActionSection
    (f : X ⟶ Y) (M : X.Modules) (U : Y.Opens)
    (b : Γ(X,f ⁻¹ᵁ U)) (x : Γ((Scheme.Modules.pushforward f).obj M,U)) :
    Γ((Scheme.Modules.pushforward f).obj M,U) :=
  (show Γ(M,f ⁻¹ᵁ U) from b • (show Γ(M,f ⁻¹ᵁ U) from x))

theorem schemePushforwardOriginalSourceActionSection_from_source_module
    (f : X ⟶ Y) (M : X.Modules) (U : Y.Opens)
    (b : Γ(X,f ⁻¹ᵁ U)) (x : Γ((Scheme.Modules.pushforward f).obj M,U)) :
    schemePushforwardOriginalSourceActionSection f M U b x =
      (show Γ((Scheme.Modules.pushforward f).obj M,U) from
        (show ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf).obj.obj (op U) from b) •
        (show (schemePushforwardSourceModuleSheaf f M).val.obj (op U) from x)) := rfl
end LinearStudy
