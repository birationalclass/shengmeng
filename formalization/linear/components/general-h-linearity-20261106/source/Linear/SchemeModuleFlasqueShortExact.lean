module
public import Linear.SchemeModuleInjectiveFlasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {S : ShortComplex X.Modules}
/-- Flasque actual modules are closed under quotients by an actual injective middle term. -/
theorem schemeModule_flasque_quotient_of_injective (hS : S.ShortExact)
    (hF : TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj S.X₁))
    (hI : Injective S.X₂) :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj S.X₃) := by
  letI := hI
  letI : TopCat.Sheaf.IsFlasque (S.map (schemeModuleToAdditiveSheaf X)).X₁ := hF
  letI : TopCat.Sheaf.IsFlasque (S.map (schemeModuleToAdditiveSheaf X)).X₂ :=
    schemeModule_injective_isFlasque X S.X₂
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
    (schemeModuleShortExact_underlyingAdditiveSheaf S hS)

/-- A short exact sequence with actual flasque first term lifts every original global unit morphism. -/
theorem schemeModule_shortExact_unitHom_lift_of_flasque (hS : S.ShortExact)
    (hF : TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj S.X₁))
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃) :
    ∃ g : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₂, g ≫ S.g = f := by
  have ha := schemeModuleShortExact_underlyingAdditiveSheaf S hS
  letI : TopCat.Sheaf.IsFlasque
      (S.map (schemeModuleToAdditiveSheaf X)).X₁ := hF
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) ha
  obtain ⟨s,hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp he
    (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤)))
  change Scheme.Modules.Hom.app S.g ⊤ s =
    Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤)) at hs
  refine ⟨moduleSheafGlobalSectionMorphism S.X₂ s, ?_⟩
  rw [← moduleSheafGlobalSectionMorphism_postcompose,hs,
    moduleSheafGlobalSectionMorphism_of_morphism]
end LinearStudy
