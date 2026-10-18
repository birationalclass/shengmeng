module
public import Linear.SchemeModuleClosedDiscreteGlobalToInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
/-- The canonical lambda map into ORIGINAL top-open sections is bijective for actual closed discrete direct image, for every positive degree and arbitrary coefficient. -/
theorem schemeModuleGlobalToInternalExtSections_closedDiscrete_bijective
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) (N : X.Modules) (n : ℕ) :
    Function.Bijective
      (schemeModuleGlobalToInternalExtSections ((Scheme.Modules.pushforward f).obj L) N n) := by
  let P := (Scheme.Modules.pushforward f).obj L
  let E := schemeModuleInternalExt P N (n+1)
  have he : Function.Bijective
      (fun a : SheafOfModules.unit X.ringCatSheaf ⟶ E =>
        Scheme.Modules.Hom.app a ⊤ (1 : Γ(X,⊤))) := by
    constructor
    · intro a b hab
      rw [← moduleSheafGlobalSectionMorphism_of_morphism E a,
        ← moduleSheafGlobalSectionMorphism_of_morphism E b]
      exact congrArg (moduleSheafGlobalSectionMorphism E) hab
    · intro s
      exact ⟨moduleSheafGlobalSectionMorphism E s,
        moduleSheafGlobalSectionMorphism_app_top_one E s⟩
  exact he.comp (schemeModuleGlobalToInternalExt_closedDiscrete_bijective f hf L N n)
/-- The actual finite/Artinian closed cut has the SAME canonical global-Ext-to-derived-SHEAF-Ext-section isomorphism. No coefficient freeness, flatness or quasi-coherence is required. -/
theorem schemeModuleGlobalToInternalExtSections_artinianClosedImmersion_bijective
    {D X : Scheme.{u}} [IsArtinianScheme D] (f : D ⟶ X) [IsClosedImmersion f]
    (L : D.Modules) (N : X.Modules) (n : ℕ) :
    Function.Bijective
      (schemeModuleGlobalToInternalExtSections ((Scheme.Modules.pushforward f).obj L) N n) :=
  schemeModuleGlobalToInternalExtSections_closedDiscrete_bijective f
    f.isClosedEmbedding.isClosedMap L N n
end LinearStudy
