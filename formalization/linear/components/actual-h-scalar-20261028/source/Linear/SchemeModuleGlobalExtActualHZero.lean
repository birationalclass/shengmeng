module
public import Linear.ExtZeroHomCoefficientNaturality
public import Linear.SchemeModuleFlasqueKernelSectionLifting
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
variable (X : Scheme.{u})
/-- Actual unit morphisms identify additively with original top-open sections. -/
def schemeModuleUnitHomGlobalSectionsAddEquiv (F : X.Modules) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ F) ≃+ Γ(F,⊤) where
  toFun f := Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤))
  invFun := moduleSheafGlobalSectionMorphism F
  left_inv := moduleSheafGlobalSectionMorphism_of_morphism F
  right_inv := moduleSheafGlobalSectionMorphism_app_top_one F
  map_add' f g := rfl

/-- Original GLOBAL Ext degree zero,with its actual section-valued comparison. -/
def schemeModuleGlobalExtZeroSectionsAddEquiv (F : X.Modules) :
    Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F 0 ≃+ Γ(F,⊤) :=
  Ext.addEquiv₀.trans (schemeModuleUnitHomGlobalSectionsAddEquiv X F)

/-- Degree-zero comparison with NATIVE actual underlying-abelian SHEAF cohomology. -/
def schemeModuleGlobalExtZeroActualHAddEquiv (F : X.Modules) :
    Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F 0 ≃+
      schemeModuleActualCohomology X F 0 :=
  (schemeModuleGlobalExtZeroSectionsAddEquiv X F).trans
    (CategoryTheory.Sheaf.H.equiv₀ ((schemeModuleToActualAbelianSheaf X).obj F)
      isTerminalTop).symm

/-- The degree-zero comparison is exactly evaluation of the same unit morphism at one. -/
theorem schemeModuleGlobalExtZeroActualHAddEquiv_evaluate (F : X.Modules)
    (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F 0) :
    CategoryTheory.Sheaf.H.equiv₀ ((schemeModuleToActualAbelianSheaf X).obj F) isTerminalTop
      (schemeModuleGlobalExtZeroActualHAddEquiv X F x) =
        Scheme.Modules.Hom.app (Ext.addEquiv₀ x) ⊤ (1 : Γ(X,⊤)) :=
  (CategoryTheory.Sheaf.H.equiv₀ ((schemeModuleToActualAbelianSheaf X).obj F)
    isTerminalTop).apply_symm_apply _

/-- The actual degree-zero comparison commutes with every original coefficient morphism. -/
theorem schemeModuleGlobalExtZeroActualHAddEquiv_naturality {F G : X.Modules}
    (f : F ⟶ G) (x : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F 0) :
    schemeModuleGlobalExtZeroActualHAddEquiv X G (x.comp (Ext.mk₀ f) (add_zero 0)) =
      CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map f) 0
        (schemeModuleGlobalExtZeroActualHAddEquiv X F x) := by
  apply (CategoryTheory.Sheaf.H.equiv₀ ((schemeModuleToActualAbelianSheaf X).obj G)
    isTerminalTop).injective
  calc
    _ = Scheme.Modules.Hom.app (Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0))) ⊤
          (1 : Γ(X,⊤)) := schemeModuleGlobalExtZeroActualHAddEquiv_evaluate X G _
    _ = Scheme.Modules.Hom.app f ⊤
          (Scheme.Modules.Hom.app (Ext.addEquiv₀ x) ⊤ (1 : Γ(X,⊤))) :=
        congrArg (fun (a : SheafOfModules.unit X.ringCatSheaf ⟶ G) =>
          Scheme.Modules.Hom.app a ⊤ (1 : Γ(X,⊤)))
          (extZeroHomEquiv_postcompose (SheafOfModules.unit X.ringCatSheaf) f x)
    _ = Scheme.Modules.Hom.app f ⊤
          (CategoryTheory.Sheaf.H.equiv₀ ((schemeModuleToActualAbelianSheaf X).obj F)
            isTerminalTop (schemeModuleGlobalExtZeroActualHAddEquiv X F x)) :=
        congrArg (Scheme.Modules.Hom.app f ⊤)
          (schemeModuleGlobalExtZeroActualHAddEquiv_evaluate X F x).symm
    _ = _ := CategoryTheory.Sheaf.H.equiv₀_naturality
      isTerminalTop ((schemeModuleToActualAbelianSheaf X).map f) _
end LinearStudy
