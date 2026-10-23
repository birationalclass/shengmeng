module
public import Linear.SchemeModuleScalarNaturality
public import Linear.SchemeModuleGlobalExtActualHCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- ORIGINAL global coefficient multiplication is central in EVERY
actual GLOBAL module Ext degree. Reuses exact-functor Ext naturality;
no scalar compatibility of the desired boundary is assumed. -/
theorem schemeModuleGlobalScalar_ext_centrality
    (X : Scheme.{u}) (z : Γ(X,⊤)) {M N : X.Modules} (r : ℕ)
    (epsilon : Ext.{u} M N r) :
    epsilon.comp (Ext.mk₀ (originalGlobalModuleScalar z N)) (add_zero r) =
      (Ext.mk₀ (originalGlobalModuleScalar z M)).comp epsilon (zero_add r) := by
  let tau : 𝟭 X.Modules ⟶ 𝟭 X.Modules := {
    app := originalGlobalModuleScalar z
    naturality := fun M N f => (originalGlobalModuleScalar_naturality z f).symm }
  simpa only [Ext.id_mapExactFunctor] using
    Ext.mapExactFunctor_comp_mk₀_natTransApp epsilon tau
end LinearStudy
