module
public import Linear.SchemeModuleGlobalToInternalExtAllDegrees
public import Linear.SchemeModuleGlobalToInternalExtSourceNaturality
public import Linear.SchemeModuleInternalExtZeroSource
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
/-- The ACTUAL Hom-to-internalExt0 map retains SAME source precomposition. -/
theorem schemeModuleHomToInternalExtZero_sourceNaturality {P Q N : X.Modules}
    (g : P ⟶ Q) (a : Q ⟶ N) :
    schemeModuleHomToInternalExtZero P N (g ≫ a) =
      schemeModuleHomToInternalExtZero Q N a ≫ schemeModuleInternalExtSourceMap g N 0 := by
  change (schemeModuleHomUnitAddEquiv P N).symm (g ≫ a) ≫
    ((schemeModuleInternalExtZeroIso P).app N).inv =
      ((schemeModuleHomUnitAddEquiv Q N).symm a ≫ ((schemeModuleInternalExtZeroIso Q).app N).inv) ≫ _
  rw [schemeModuleHomUnitAddEquiv_symm_precompose,Category.assoc,
    schemeModuleInternalExtZeroIso_source_inv,← Category.assoc]
/-- ACTUAL canonical comparison is source-natural in EVERY degree,including Hom,without a desired naturality input. -/
theorem schemeModuleGlobalToInternalExtAll_sourceNaturality {P Q N : X.Modules}
    (g : P ⟶ Q) (q : ℕ) (e : Ext.{u} Q N q) :
    schemeModuleGlobalToInternalExtAll P N q ((Ext.mk₀ g).comp e (zero_add _)) =
      schemeModuleGlobalToInternalExtAll Q N q e ≫ schemeModuleInternalExtSourceMap g N q := by
  cases q with
  | zero =>
    obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective Q N).surjective e
    rw [Ext.mk₀_comp_mk₀,schemeModuleGlobalToInternalExtAll_mkZero,
      schemeModuleGlobalToInternalExtAll_mkZero]
    exact schemeModuleHomToInternalExtZero_sourceNaturality g a
  | succ n =>
    rw [schemeModuleGlobalToInternalExtAll_succ,schemeModuleGlobalToInternalExtAll_succ]
    exact schemeModuleGlobalToInternalExt_sourceNaturality g n e
end LinearStudy
