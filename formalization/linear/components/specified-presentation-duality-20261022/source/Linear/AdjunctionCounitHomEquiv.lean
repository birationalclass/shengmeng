module
public import Mathlib.CategoryTheory.Adjunction.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}
/-- Generic counit identity is checked before specializing the original geometric objects. -/
theorem adjunction_homEquiv_map_counit (adj : F ⊣ G) (X : C) (Y : D)
    (g : X ⟶ G.obj Y) : adj.homEquiv X Y (F.map g ≫ adj.counit.app Y) = g := by
  rw [← Adjunction.homEquiv_counit]
  exact Equiv.apply_symm_apply _ _
end LinearStudy
