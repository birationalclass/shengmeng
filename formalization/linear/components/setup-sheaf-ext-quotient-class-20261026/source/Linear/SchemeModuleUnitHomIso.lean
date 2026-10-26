module
public import Linear.SchemeModuleUnitHomSections
public import Linear.SchemeModuleInternalHomCoefficientFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The actual unit/internal-Hom section comparison is O(U)-linear. -/
def schemeModuleUnitHomSectionsLinearEquiv (N : X.Modules) (U : X.Opens) :
    Γ(schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N,U) ≃ₗ[Γ(X,U)] Γ(N,U) where
  toEquiv := schemeModuleUnitHomSectionsEquiv N U
  map_add' f g := rfl
  map_smul' r f := by
    change X.presheaf.map (𝟙 U).op r •
        (show Γ(N,U) from f.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U))) =
      r • (show Γ(N,U) from f.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U)))
    simp

/-- Evaluation at 1 commutes with SAME original open restrictions. -/
theorem schemeModuleUnitHomSectionsEquiv_restrict (N : X.Modules) {U V : X.Opens}
    (i : V ⟶ U)
    (f : Γ(schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N,U)) :
    schemeModuleUnitHomSectionsEquiv N V
      ((schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N).presheaf.map i.op f) =
      N.presheaf.map i.op (schemeModuleUnitHomSectionsEquiv N U f) := by
  have h := schemeModuleHomSectionEvaluation_restrict
    (SheafOfModules.unit X.ringCatSheaf) N i f (1 : Γ(X,U))
  have h1 : (Scheme.Modules.presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).map i.op
      (1 : Γ(X,U)) = (1 : Γ(X,V)) := by
    change X.presheaf.map i.op (1 : Γ(X,U)) = 1
    exact map_one (X.presheaf.map i.op).hom
  rw [h1] at h
  exact h

/-- ACTUAL O_X-linear internal Hom from the SAME structure sheaf is N. -/
def schemeModuleUnitHomIso (N : X.Modules) :
    schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N ≅ N :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk
      (fun U => (schemeModuleUnitHomSectionsLinearEquiv N U.unop).toModuleIso)
      (by
        intro U V i
        ext f
        exact schemeModuleUnitHomSectionsEquiv_restrict N i.unop f))

/-- The actual unit isomorphism retains original local evaluation at 1. -/
theorem schemeModuleUnitHomIso_hom_app (N : X.Modules) (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf (SheafOfModules.unit X.ringCatSheaf) N,U)) :
    (schemeModuleUnitHomIso N).hom.app U f =
      f.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U)) := rfl

/-- The SAME unit/internal-Hom isomorphism is natural in every actual coefficient. -/
def schemeModuleInternalHomUnitCoefficientIso (X : Scheme.{u}) :
    schemeModuleInternalHomCoefficientFunctor X (SheafOfModules.unit X.ringCatSheaf) ≅
      𝟭 X.Modules :=
  NatIso.ofComponents schemeModuleUnitHomIso (by
    intro M N c
    apply SheafOfModules.hom_ext
    ext U f
    change ((schemeModuleHomPostcompose c).app U.unop f).val.app
        (op (Over.mk (𝟙 U.unop))) (1 : Γ(X,U.unop)) =
      c.app U.unop (f.val.app (op (Over.mk (𝟙 U.unop))) (1 : Γ(X,U.unop)))
    rfl)

end LinearStudy
