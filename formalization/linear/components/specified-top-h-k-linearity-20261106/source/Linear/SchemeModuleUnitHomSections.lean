module
public import Linear.SchemeModuleHomEvaluationRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual sections over Over(U) are actual original sections on U. -/
def schemeModuleOverSectionsEquiv (N : X.Modules) (U : X.Opens) :
    (N.over U).sections ≃ Γ(N,U) where
  toFun s := s.val (op (Over.mk (𝟙 U)))
  invFun n := ⟨fun W => N.presheaf.map W.unop.hom.op n,by
    intro W V i
    change N.presheaf.map i.unop.left.op
      (N.presheaf.map W.unop.hom.op n) = N.presheaf.map V.unop.hom.op n
    have h : N.presheaf.map W.unop.hom.op ≫ N.presheaf.map i.unop.left.op =
        N.presheaf.map V.unop.hom.op := by
      rw [← N.presheaf.map_comp,← op_comp,i.unop.w]
    exact congr($(h) n)⟩
  left_inv s := by
    apply Subtype.ext
    funext W
    exact s.property (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op
  right_inv n := by
    change N.presheaf.map (𝟙 U).op n = n
    simp

/-- The SAME native structure-sheaf unit restricts to the unit on Over(U). -/
def schemeModuleUnitOverIso (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := Iso.refl _

/-- Actual internal Hom from the structure sheaf,section by original section. -/
def schemeModuleUnitHomSectionsEquiv (N : X.Modules) (U : X.Opens) :
    Γ(schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N,U) ≃ Γ(N,U) :=
  (schemeModuleHomModuleSectionsEquiv (SheafOfModules.unit X.ringCatSheaf) N U).trans
    ((Iso.homCongr (schemeModuleUnitOverIso X U) (Iso.refl (N.over U))).trans
      ((N.over U).unitHomEquiv.trans (schemeModuleOverSectionsEquiv N U)))

/-- The actual comparison is evaluation of SAME original local functional at 1. -/
theorem schemeModuleUnitHomSectionsEquiv_apply (N : X.Modules) (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N,U)) :
    schemeModuleUnitHomSectionsEquiv N U f = f.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U)) := rfl

end LinearStudy
