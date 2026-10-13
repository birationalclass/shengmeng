module
public import Linear.SchemeModuleGlobalSectionMorphism
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- Actual closed-subscheme vanishing of an actual global section survives
any sheaf map. No claim that pullback preserves monomorphisms is used. -/
theorem moduleSheafGlobalSection_pullback_vanishing_after_map
    {X Z : Scheme.{u}} {F G : X.Modules} (i : Z ⟶ X) (j : F ⟶ G) (s : Γ(F,⊤))
    (hs : (Scheme.Modules.pullback i).map (moduleSheafGlobalSectionMorphism F s) = 0) :
    (Scheme.Modules.pullback i).map
      (moduleSheafGlobalSectionMorphism G (j.app ⊤ s)) = 0 := by
  rw [moduleSheafGlobalSectionMorphism_postcompose]
  exact moduleSheafMap_pullback_vanishing i j (moduleSheafGlobalSectionMorphism F s) hs
end LinearStudy
