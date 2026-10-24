module
public import Linear.DiscreteSchemePushforwardOpenProjector
public import Linear.SchemeModuleExtSectionTraceSourceNaturality
public import Linear.SchemeModuleGlobalToInternalExtSourceNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
universe u v
variable {D X : Scheme.{u}} [DiscreteTopology D]
/-- Project the SAME actual global Ext class by the CONSTRUCTED original
open projector on f_*L. No projector/class-fix identity is assumed. -/
def discreteSchemeProjectedExtClass (f : D ⟶ X) (L : D.Modules) (U : D.Opens)
    {W : X.Modules} {r : ℕ} (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r) :
    Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r :=
  (Ext.mk₀ (discreteSchemePushforwardOpenProjector f L U)).comp z (zero_add r)
/-- Source-fix identity is PROVED for this SAME constructed class. -/
theorem discreteSchemeProjectedExtClass_fixed
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) {W : X.Modules} {r : ℕ}
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r) :
    (Ext.mk₀ (discreteSchemePushforwardOpenProjector f L U)).comp
      (discreteSchemeProjectedExtClass f L U z) (zero_add r) =
        discreteSchemeProjectedExtClass f L U z := by
  unfold discreteSchemeProjectedExtClass
  rw [Ext.mk₀_comp_mk₀_assoc,discreteSchemePushforwardOpenProjector_idempotent]
/-- EXACT same-trace formula for the actual projected class and actual
source sections. The trace is unchanged;perfection is not asserted. -/
theorem discreteSchemeProjectedExtClass_trace
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) {W : X.Modules} {r : ℕ}
    {K : Type v} [AddCommGroup K]
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ K)
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r)
    (s : Γ((Scheme.Modules.pushforward f).obj L,⊤)) :
    schemeModuleExtSectionTracePairing trace (discreteSchemeProjectedExtClass f L U z) s =
      schemeModuleExtSectionTracePairing trace z
        ((discreteSchemePushforwardOpenProjector f L U).app ⊤ s) :=
  schemeModuleExtSectionTracePairing_source_naturality _ trace z s
/-- The actual projected class annihilates the ACTUAL complementary
source component s-b(s),with SAME trace and no supplied support identity.
This is locality of a constructed class,not nonzero local weights. -/
theorem discreteSchemeProjectedExtClass_trace_complement_zero
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) {W : X.Modules} {r : ℕ}
    {K : Type v} [AddCommGroup K]
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ K)
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r)
    (s : Γ((Scheme.Modules.pushforward f).obj L,⊤)) :
    schemeModuleExtSectionTracePairing trace (discreteSchemeProjectedExtClass f L U z)
      (s-(discreteSchemePushforwardOpenProjector f L U).app ⊤ s)=0 := by
  let b := discreteSchemePushforwardOpenProjector f L U
  have hb : b.app ⊤ (b.app ⊤ s)=b.app ⊤ s := by
    exact congrArg (fun h => Scheme.Modules.Hom.app h ⊤ s)
      (discreteSchemePushforwardOpenProjector_idempotent f L U)
  rw [discreteSchemeProjectedExtClass_trace]
  change schemeModuleExtSectionTracePairing trace z (b.app ⊤ (s-b.app ⊤ s))=0
  rw [map_sub,hb,sub_self,map_zero]
/-- The canonical global-to-INTERNAL-SHEAF-Ext section comparison retains
this SAME original projected class in every positive degree. No new
comparison map or coefficient/source isomorphism is supplied. -/
theorem discreteSchemeProjectedExtClass_internal_section
    (f : D ⟶ X) (L : D.Modules) (U : D.Opens) (W : X.Modules) (n : ℕ)
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W (n+1)) :
    schemeModuleGlobalToInternalExtSections ((Scheme.Modules.pushforward f).obj L) W n
      (discreteSchemeProjectedExtClass f L U z) =
      (schemeModuleInternalExtSourceMap (discreteSchemePushforwardOpenProjector f L U) W (n+1)).app ⊤
        (schemeModuleGlobalToInternalExtSections ((Scheme.Modules.pushforward f).obj L) W n z) :=
  schemeModuleGlobalToInternalExtSections_sourceNaturality _ n z
end LinearStudy
