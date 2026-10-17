module
public import Linear.SchemeModuleGlobalToInternalExtBoundary
public import Linear.SchemeModuleCanonicalGlobalToInternalExt
public import Linear.SchemeModuleInternalExtSourceBoundaryNaturality
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
/-- Actual resolution-independent positive global-to-internal Ext map commutes with SAME native source boundaries. -/
theorem schemeModuleGlobalToInternalExt_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (n : ℕ) (e : Ext.{u} S.X₁ N (n+1)) :
    schemeModuleGlobalToInternalExt S.X₃ N (n+1)
        (Ext.δ hS (n+1) (n+1+1) rfl e) =
      schemeModuleGlobalToInternalExt S.X₁ N n e ≫
        schemeModuleInternalExtSourceBoundary S hS N (n+1) := by
  rw [schemeModuleGlobalToInternalExt_eq_viaResolution S.X₃ N (n+1) (injectiveResolution N),
    schemeModuleGlobalToInternalExt_eq_viaResolution S.X₁ N n (injectiveResolution N),
    schemeModuleInternalExtSourceBoundary_eq_viaResolution S hS N (injectiveResolution N) (n+1)]
  exact schemeModuleGlobalToInternalExtViaResolution_boundary S hS (injectiveResolution N) n e
end LinearStudy
