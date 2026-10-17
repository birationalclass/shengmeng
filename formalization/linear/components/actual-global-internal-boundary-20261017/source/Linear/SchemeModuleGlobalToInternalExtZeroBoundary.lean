module
public import Linear.SchemeModuleHomZeroInjectiveClass
public import Linear.InjectiveNativeDegreeZeroClass
public import Linear.SchemeModuleGlobalToInternalExtBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- ACTUAL degree-zero comparison commutes with the SAME native Ext source boundary; all raw lifts are constructed. -/
theorem schemeModuleHomToInternalExtZero_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {N : X.Modules}
    (I : InjectiveResolution N) (a : S.X₁ ⟶ N) :
    schemeModuleGlobalToInternalExtViaResolution I S.X₃ 0
        (Ext.δ hS 0 1 rfl (Ext.mk₀ a)) =
      schemeModuleHomToInternalExtZero S.X₁ N a ≫
        schemeModuleInternalExtSourceBoundaryViaResolution S hS N I 0 := by
  have ha : (a ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc,I.ι_f_zero_comp_complex_d,comp_zero]
  obtain ⟨b,c,hb,hbc,hc⟩ := shortExactInjectiveNativeLifts_exists S hS I 0 (a ≫ I.ι.f 0) ha
  rw [← injectiveNativeExtMk_ofHom I a ha,
    shortExactInjectiveExtBoundary_nativeComponents S hS I 0 (a ≫ I.ι.f 0) ha b c hc hb hbc,
    schemeModuleGlobalToInternalExtViaResolution_extMk,
    schemeModuleHomToInternalExtZero_viaResolution I a ha]
  exact (schemeModuleInjectiveCocycleToInternalExt_boundary S hS I 0
    ⟨a ≫ I.ι.f 0,ha⟩ b ⟨c,hc⟩ hb hbc).symm
end LinearStudy
