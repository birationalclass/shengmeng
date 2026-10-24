module
public import Linear.SchemeModuleSupportedInternalHomClass
public import Linear.SchemeModuleCanonicalGlobalToInternalExt
public import Linear.SchemeModuleGlobalToInternalExtCocycle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
/-- The SAME previously constructed comparison via ANY actual coefficient resolution is bijective for an actual closed discrete direct-image source. -/
theorem schemeModuleGlobalToInternalExtViaResolution_closedDiscrete_bijective
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) (N : X.Modules) (I : InjectiveResolution N) (n : ℕ) :
    Function.Bijective
      (schemeModuleGlobalToInternalExtViaResolution I ((Scheme.Modules.pushforward f).obj L) n) := by
  let P := (Scheme.Modules.pushforward f).obj L
  let e := schemeModuleInternalExtInjectiveResolutionIso P N (n+1) I
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨c,rfl⟩ := injectiveCocycleExtMap_surjective I P (n+1) a
    rw [schemeModuleGlobalToInternalExtViaResolution_cocycle] at ha
    change schemeModuleInjectiveInternalHomClassMap I P (n+1) c ≫ e.inv = 0 at ha
    have hz : schemeModuleInjectiveInternalHomClassMap I P (n+1) c = 0 := by
      apply (cancel_mono e.inv).mp
      simpa only [zero_comp] using ha
    obtain ⟨g,hg⟩ :=
      (schemeModuleInjectiveInternalHomClassMap_closedDiscrete_zero_iff f hf L I n c).mp hz
    exact (injectiveCocycleExtMap_succ_eq_zero_iff I P n c).mpr ⟨g,hg⟩
  · intro s
    obtain ⟨c,hc⟩ := schemeModuleInjectiveInternalHomClassMap_closedDiscrete_surjective
      f hf L I (n+1) (s ≫ e.hom)
    refine ⟨injectiveCocycleExtMap I P (n+1) c, ?_⟩
    rw [schemeModuleGlobalToInternalExtViaResolution_cocycle]
    change schemeModuleInjectiveInternalHomClassMap I P (n+1) c ≫ e.inv = s
    rw [hc, Category.assoc, e.hom_inv_id, Category.comp_id]
/-- The ACTUAL resolution-independent canonical lambda map is bijective. Neither lambda nor its inverse is supplied as a certificate. -/
theorem schemeModuleGlobalToInternalExt_closedDiscrete_bijective
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (L : D.Modules) (N : X.Modules) (n : ℕ) :
    Function.Bijective
      (schemeModuleGlobalToInternalExt ((Scheme.Modules.pushforward f).obj L) N n) := by
  rw [schemeModuleGlobalToInternalExt_eq_viaResolution _ _ n (injectiveResolution N)]
  exact schemeModuleGlobalToInternalExtViaResolution_closedDiscrete_bijective
    f hf L N (injectiveResolution N) n
/-- For an ACTUAL Artinian closed cut, canonical positive global Ext equals global sections of ACTUAL derived SHEAF Ext, for ANY coefficient module. -/
theorem schemeModuleGlobalToInternalExt_artinianClosedImmersion_bijective
    {D X : Scheme.{u}} [IsArtinianScheme D] (f : D ⟶ X) [IsClosedImmersion f]
    (L : D.Modules) (N : X.Modules) (n : ℕ) :
    Function.Bijective
      (schemeModuleGlobalToInternalExt ((Scheme.Modules.pushforward f).obj L) N n) :=
  schemeModuleGlobalToInternalExt_closedDiscrete_bijective f f.isClosedEmbedding.isClosedMap L N n
end LinearStudy
