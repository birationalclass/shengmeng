module
public import Linear.SchemeModuleHomModuleSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}

/-- For the original topological space, a compatible section family is
exactly its section on the whole original space. -/
def originalPresheafTopSectionsEquiv (F : X.Opensᵒᵖ ⥤ Type u) :
    F.sections ≃ F.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun x := {
    val U := F.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x
    property i := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp]
      congr 1 }
  left_inv s := by
    apply Subtype.ext
    funext U
    exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  right_inv x := by
    change F.map (𝟙 (op ⊤)) x = x
    rw [F.map_id]
    rfl

/-- ACTUAL sections of the internal Hom O-module on the whole ORIGINAL
scheme correspond to actual original global module-sheaf morphisms. -/
def schemeModuleHomTopSectionsEquiv (M N : X.Modules) :
    Γ(schemeModuleHomModuleSheaf M N,⊤) ≃ (M ⟶ N) :=
  (originalPresheafTopSectionsEquiv (schemeModuleHomPresheaf M N)).symm.trans
    (schemeModuleHomGlobalEquiv M N)

end LinearStudy
