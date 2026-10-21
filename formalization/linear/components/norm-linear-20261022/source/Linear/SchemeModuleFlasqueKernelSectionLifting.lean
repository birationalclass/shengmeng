module
public import Linear.SchemeModuleAdditiveSheafColimits
public import Linear.SchemeModuleFiniteSupportCohomology
public import Linear.SchemeModuleGlobalSectionMorphism
public import Mathlib.Topology.Sheaves.Flasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
/-- A morphism from the ACTUAL structure module is recovered from its ACTUAL value at one on the top open. -/
theorem moduleSheafGlobalSectionMorphism_of_morphism {X : Scheme.{u}} (M : X.Modules)
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    moduleSheafGlobalSectionMorphism M (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤))) = f := by
  apply M.unitHomEquiv.injective
  simp only [moduleSheafGlobalSectionMorphism, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤))) = Scheme.Modules.Hom.app f U.unop (1 : Γ(X,U.unop))
  have h := moduleSheafMap_restriction_apply f (show U.unop ≤ ⊤ from le_top) (1 : Γ(X,⊤))
  have hone : (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).map
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : Γ(X,⊤)) = (1 : Γ(X,U.unop)) := by
    change X.presheaf.map _ (1 : Γ(X,⊤)) = 1
    exact map_one _
  rw [hone] at h
  exact h
/-- An actual epi whose actual kernel is flasque is surjective on every original section group. No projectivity of O_X is assumed. -/
theorem schemeModule_epi_sections_surjective_of_flasqueKernel {X : Scheme.{u}}
    {M N : X.Modules} (g : M ⟶ N) [Epi g]
    (hker : TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj (kernel g)))
    (U : X.Opens) : Function.Surjective (g.app U) := by
  letI : Epi (ShortComplex.kernelSequence g).g := (inferInstance : Epi g)
  have hs : (ShortComplex.kernelSequence g).ShortExact :=
    ⟨ShortComplex.kernelSequence_exact g⟩
  have ha := schemeModuleShortExact_underlyingAdditiveSheaf (ShortComplex.kernelSequence g) hs
  letI : TopCat.Sheaf.IsFlasque
      ((ShortComplex.kernelSequence g).map (schemeModuleToAdditiveSheaf X)).X₁ := hker
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) ha
  exact (AddCommGrpCat.epi_iff_surjective _).mp he
/-- Lift an actual unit morphism through the SAME original epi using flasque-kernel section lifting. -/
theorem schemeModule_unitHom_lift_of_flasqueKernel {X : Scheme.{u}}
    {M N : X.Modules} (g : M ⟶ N) [Epi g]
    (hker : TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj (kernel g)))
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    ∃ e : SheafOfModules.unit X.ringCatSheaf ⟶ M, e ≫ g = f := by
  obtain ⟨s,hs⟩ := schemeModule_epi_sections_surjective_of_flasqueKernel g hker ⊤
    (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤)))
  refine ⟨moduleSheafGlobalSectionMorphism M s, ?_⟩
  rw [← moduleSheafGlobalSectionMorphism_postcompose, hs,
    moduleSheafGlobalSectionMorphism_of_morphism]
end LinearStudy
