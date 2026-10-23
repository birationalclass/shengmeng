module
public import Linear.SchemeModuleInjectiveCocycleBoundary
public import Linear.ShortExactInjectiveNativeBoundaryComponents
public import Linear.ShortExactInjectiveNativeLifts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- The ACTUAL positive global-to-internal Ext map commutes with native
source connecting maps for EVERY short exact source sequence and ANY SAME
coefficient injective resolution. CONSTRUCT raw lifts;no desired boundary
square,class identity or projectivity premise is supplied. -/
theorem schemeModuleGlobalToInternalExtViaResolution_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {N : X.Modules}
    (I : InjectiveResolution N) (n : ℕ) (e : Ext.{u} S.X₁ N (n+1)) :
    schemeModuleGlobalToInternalExtViaResolution I S.X₃ (n+1)
        (Ext.δ hS (n+1) (n+1+1) rfl e) =
      schemeModuleGlobalToInternalExtViaResolution I S.X₁ n e ≫
        schemeModuleInternalExtSourceBoundaryViaResolution S hS N I (n+1) := by
  obtain ⟨a,ha,rfl⟩ := I.extMk_surjective e (n+1+1) rfl
  obtain ⟨b,c,hb,hbc,hc⟩ := shortExactInjectiveNativeLifts_exists S hS I (n+1) a ha
  rw [shortExactInjectiveExtBoundary_nativeComponents S hS I (n+1) a ha b c hc hb hbc,
    schemeModuleGlobalToInternalExtViaResolution_extMk,
    schemeModuleGlobalToInternalExtViaResolution_extMk]
  exact (schemeModuleInjectiveCocycleToInternalExt_boundary S hS I (n+1)
    ⟨a,ha⟩ b ⟨c,hc⟩ hb hbc).symm

end LinearStudy
