module
public import Linear.SchemeModuleSupportedSubHomFlasque
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Actual pushforward has zero sections on opens disjoint from the actual map range. -/
theorem schemeModulePushforward_sections_subsingleton_of_disjointRange
    {D X : Scheme.{u}} (f : D ⟶ X) (L : D.Modules) (U : X.Opens)
    (hU : Disjoint (U : Set X) (Set.range f)) :
    Subsingleton Γ((Scheme.Modules.pushforward f).obj L, U) := by
  have he : f ⁻¹ᵁ U = ⊥ := by
    apply le_antisymm
    · intro x hx
      exact (Set.disjoint_left.mp hU hx ⟨x,rfl⟩).elim
    · exact bot_le
  change Subsingleton Γ(L, f ⁻¹ᵁ U)
  exact abelianSheaf_sections_subsingleton_of_eq_empty
    ((schemeModuleToActualAbelianSheaf D).obj L) he
/-- Derive vanishing of the ORIGINAL direct image on every open disjoint from its actual support. -/
theorem schemeModulePushforward_open_isZero_of_disjointRange
    {D X : Scheme.{u}} (f : D ⟶ X) (L : D.Modules) (U : X.Opens)
    (hU : Disjoint (U : Set X) (Set.range f)) :
    IsZero (((Scheme.Modules.pushforward f).obj L).restrict U.ι) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SheafOfModules.hom_ext
  ext V s
  let W : X.Opens := U.ι ''ᵁ V.unop
  have hWU : (W : Set X) ⊆ (U : Set X) := by
    rintro x ⟨y,hy,rfl⟩
    exact y.property
  have hW : Disjoint (W : Set X) (Set.range f) := hU.mono_left hWU
  change (s : Γ((Scheme.Modules.pushforward f).obj L, W)) = 0
  exact (schemeModulePushforward_sections_subsingleton_of_disjointRange f L W hW).elim _ _
/-- For ANY coefficient N, every actual subobject of Hom(f_*L,N) is flasque when f is closed with discrete source. -/
theorem schemeModuleSubHom_pushforward_closedDiscreteFlasque
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) (N M : X.Modules)
    (g : M ⟶ schemeModuleHomModuleSheaf ((Scheme.Modules.pushforward f).obj L) N) [Mono g] :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj M) := by
  apply schemeModuleSubHom_closedDiscreteFlasque f hf _ N M g
  exact fun U hU => schemeModulePushforward_open_isZero_of_disjointRange f L U hU
/-- Actual Artinian closed cuts supply the support hypotheses; arbitrary coefficients, cycles and boundaries are allowed. -/
theorem schemeModuleSubHom_artinianClosedImmersionFlasque
    {D X : Scheme.{u}} [IsArtinianScheme D] (f : D ⟶ X) [IsClosedImmersion f]
    (L : D.Modules) (N M : X.Modules)
    (g : M ⟶ schemeModuleHomModuleSheaf ((Scheme.Modules.pushforward f).obj L) N) [Mono g] :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj M) :=
  schemeModuleSubHom_pushforward_closedDiscreteFlasque f f.isClosedEmbedding.isClosedMap L N M g
end LinearStudy
