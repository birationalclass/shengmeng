module
public import Linear.SheafEmbeddingSectionTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (F : X.Modules)

/-- The family of ACTUAL restrictions of one actual global section.
The family has proved naturality; no compatible-section data are assumed. -/
def moduleSheafGlobalSectionFamily (s : Γ(F,⊤)) : F.sections :=
  PresheafOfModules.sectionsMk (fun U =>
    F.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) (by
      intro U V f
      change F.presheaf.map f
        (F.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) =
        F.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s
      exact (ConcreteCategory.congr_hom (F.presheaf.map_comp
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op f) s).symm.trans
        (congrArg (fun k => F.presheaf.map k s) (Subsingleton.elim _ _)))

/-- Use mathlib's ACTUAL unit-Hom equivalence to represent the original
global section as a morphism from the actual structure module. -/
def moduleSheafGlobalSectionMorphism (s : Γ(F,⊤)) :
    SheafOfModules.unit.{u} X.ringCatSheaf ⟶ F :=
  F.unitHomEquiv.symm (moduleSheafGlobalSectionFamily F s)

theorem moduleSheafGlobalSectionMorphism_app_top_one (s : Γ(F,⊤)) :
    Scheme.Modules.Hom.app (moduleSheafGlobalSectionMorphism F s) ⊤ (1 : Γ(X,⊤)) = s := by
  have h := congrArg (fun t : F.sections => t.val (op ⊤))
    (F.unitHomEquiv.apply_symm_apply (moduleSheafGlobalSectionFamily F s))
  change Scheme.Modules.Hom.app (moduleSheafGlobalSectionMorphism F s) ⊤ (1 : Γ(X,⊤)) =
    F.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op s at h
  have hid : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  simpa only [hid,F.presheaf.map_id,ConcreteCategory.id_apply] using h

theorem moduleSheafGlobalSectionMorphism_ne_zero (s : Γ(F,⊤)) (hs : s ≠ 0) :
    moduleSheafGlobalSectionMorphism F s ≠ 0 := by
  intro hz
  apply hs
  rw [← moduleSheafGlobalSectionMorphism_app_top_one F s,hz]
  rfl

/-- The ACTUAL global-section morphism commutes with any actual sheaf
map. This is the bridge needed to preserve closed-subscheme vanishing. -/
theorem moduleSheafGlobalSectionMorphism_postcompose {G : X.Modules}
    (j : F ⟶ G) (s : Γ(F,⊤)) :
    moduleSheafGlobalSectionMorphism G (j.app ⊤ s) =
      moduleSheafGlobalSectionMorphism F s ≫ j := by
  apply G.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  simp only [moduleSheafGlobalSectionMorphism,Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  exact moduleSheafMap_restriction_apply j (show U.unop ≤ ⊤ from le_top) s
end LinearStudy
