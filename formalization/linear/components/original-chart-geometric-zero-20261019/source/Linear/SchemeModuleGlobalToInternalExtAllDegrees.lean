module
public import Linear.SchemeModuleGlobalToInternalExtZeroBoundary
public import Linear.SchemeModuleCanonicalGlobalToInternalExtBoundary
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
/-- ACTUAL canonical global-to-internal Ext map in EVERY degree,including native Hom in degree zero. -/
def schemeModuleGlobalToInternalExtAll (P N : X.Modules) (q : ℕ) :
    Ext.{u} P N q →+ (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N q) :=
  match q with
  | 0 => (schemeModuleHomToInternalExtZero P N).comp Ext.addEquiv₀.toAddMonoidHom
  | n+1 => schemeModuleGlobalToInternalExt P N n
/-- EXACT zero-degree formula without expanding any derived resolution. -/
theorem schemeModuleGlobalToInternalExtAll_zero (P N : X.Modules) :
    schemeModuleGlobalToInternalExtAll P N 0 =
      (schemeModuleHomToInternalExtZero P N).comp Ext.addEquiv₀.toAddMonoidHom := rfl
/-- EXACT positive-degree formula retaining the already proved canonical map. -/
theorem schemeModuleGlobalToInternalExtAll_succ (P N : X.Modules) (n : ℕ) :
    schemeModuleGlobalToInternalExtAll P N (n+1) = schemeModuleGlobalToInternalExt P N n := rfl
/-- The all-degree map retains the EXACT actual original sheaf morphism at degree zero. -/
theorem schemeModuleGlobalToInternalExtAll_mkZero (P N : X.Modules) (a : P ⟶ N) :
    schemeModuleGlobalToInternalExtAll P N 0 (Ext.mk₀ a) =
      schemeModuleHomToInternalExtZero P N a := by
  change schemeModuleHomToInternalExtZero P N (Ext.addEquiv₀ (Ext.mk₀ a)) = _
  congr 1
  exact Ext.addEquiv₀.apply_symm_apply a
/-- The actual comparison commutes with EVERY SAME native source connecting map,including the essential initial Hom-to-Ext1 step. -/
theorem schemeModuleGlobalToInternalExtAll_boundary
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (q : ℕ) (e : Ext.{u} S.X₁ N q) :
    schemeModuleGlobalToInternalExtAll S.X₃ N (q+1) (Ext.δ hS q (q+1) rfl e) =
      schemeModuleGlobalToInternalExtAll S.X₁ N q e ≫
        schemeModuleInternalExtSourceBoundary S hS N q := by
  cases q with
  | zero =>
    obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective S.X₁ N).surjective e
    rw [schemeModuleGlobalToInternalExtAll_mkZero,
      schemeModuleGlobalToInternalExtAll_succ,
      schemeModuleGlobalToInternalExt_eq_viaResolution S.X₃ N 0 (injectiveResolution N),
      schemeModuleInternalExtSourceBoundary_eq_viaResolution S hS N (injectiveResolution N) 0]
    exact schemeModuleHomToInternalExtZero_boundary S hS (injectiveResolution N) a
  | succ n =>
    rw [schemeModuleGlobalToInternalExtAll_succ,schemeModuleGlobalToInternalExtAll_succ]
    exact schemeModuleGlobalToInternalExt_boundary S hS N n e
end LinearStudy
