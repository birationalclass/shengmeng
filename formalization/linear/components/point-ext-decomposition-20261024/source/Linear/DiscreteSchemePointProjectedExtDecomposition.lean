module
public import Linear.DiscreteSchemePointIdempotents
public import Linear.DiscreteSchemeProjectedExtTrace
public import Linear.OriginalGlobalModuleScalarRingHom
public import Linear.FiniteCutArtinianTopology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open scoped BigOperators
universe u v
/-- Actual source projector selecting one original point of D. -/
def discreteSchemePushforwardPointProjector {D X : Scheme.{u}} [DiscreteTopology D]
    (f : D ⟶ X) (L : D.Modules) (x : D) :
    (Scheme.Modules.pushforward f).obj L ⟶ (Scheme.Modules.pushforward f).obj L :=
  discreteSchemePushforwardOpenProjector f L (discreteSchemePointOpen D x)
/-- The ACTUAL source point projectors sum to identity. No decomposition
or source identity is supplied as input. -/
theorem discreteSchemePushforwardPointProjector_sum
    {D X : Scheme.{u}} [DiscreteTopology D] [Fintype D]
    (f : D ⟶ X) (L : D.Modules) :
    (∑ x : D,discreteSchemePushforwardPointProjector f L x)=𝟙 _ := by
  classical
  have hs := congrArg (fun e : Γ(D,⊤) => (originalGlobalModuleScalarRingHom L) e)
    (discreteSchemePointIdempotent_sum D)
  rw [map_sum,map_one] at hs
  change (∑ x : D,(Scheme.Modules.pushforward f).map
    ((originalGlobalModuleScalarRingHom L) (discreteSchemePointIdempotent D x)))=𝟙 _
  rw [← Functor.map_sum,hs]
  exact (Scheme.Modules.pushforward f).map_id L
/-- Distinct ACTUAL point projectors are orthogonal after pushforward. -/
theorem discreteSchemePushforwardPointProjector_comp_eq_zero
    {D X : Scheme.{u}} [DiscreteTopology D]
    (f : D ⟶ X) (L : D.Modules) (x y : D) (hxy : x ≠ y) :
    discreteSchemePushforwardPointProjector f L x ≫
      discreteSchemePushforwardPointProjector f L y=0 := by
  change (Scheme.Modules.pushforward f).map
      (originalGlobalModuleScalar (discreteSchemePointIdempotent D x) L) ≫
    (Scheme.Modules.pushforward f).map
      (originalGlobalModuleScalar (discreteSchemePointIdempotent D y) L)=0
  rw [← Functor.map_comp,← originalGlobalModuleScalar_mul,
    discreteSchemePointIdempotent_mul_eq_zero D y x hxy.symm,
    originalGlobalModuleScalar_zero,Functor.map_zero]
/-- The SAME actual global Ext class projected at one original point. -/
def discreteSchemePointProjectedExtClass {D X : Scheme.{u}} [DiscreteTopology D]
    (f : D ⟶ X) (L : D.Modules) (x : D) {W : X.Modules} {r : ℕ}
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r) :
    Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r :=
  discreteSchemeProjectedExtClass f L (discreteSchemePointOpen D x) z
/-- Every original global Ext class is the sum of its ACTUAL point
components. Source,coefficient,degree and Ext class are unchanged. -/
theorem discreteSchemePointProjectedExtClass_sum
    {D X : Scheme.{u}} [DiscreteTopology D] [Fintype D]
    (f : D ⟶ X) (L : D.Modules) {W : X.Modules} {r : ℕ}
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r) :
    (∑ x : D,discreteSchemePointProjectedExtClass f L x z)=z := by
  classical
  change (∑ x : D,(Ext.mk₀ (discreteSchemePushforwardPointProjector f L x)).comp z (zero_add r))=z
  rw [← Ext.sum_comp,← Ext.mk₀_sum,discreteSchemePushforwardPointProjector_sum,Ext.mk₀_id_comp]
/-- The SAME arbitrary trace pairing decomposes into these ACTUAL point
classes. In particular this applies to the constructed model trace;no
new perfect functional is selected. Nonzero point weights remain OPEN. -/
theorem discreteSchemePointProjectedExtClass_trace_sum
    {D X : Scheme.{u}} [DiscreteTopology D] [Fintype D]
    (f : D ⟶ X) (L : D.Modules) {W : X.Modules} {r : ℕ}
    {K : Type v} [AddCommGroup K]
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ K)
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r)
    (s : Γ((Scheme.Modules.pushforward f).obj L,⊤)) :
    schemeModuleExtSectionTracePairing trace z s=
      ∑ x : D,schemeModuleExtSectionTracePairing trace (discreteSchemePointProjectedExtClass f L x z) s := by
  classical
  calc
    _ = schemeModuleExtSectionTracePairing trace
        (∑ x : D,discreteSchemePointProjectedExtClass f L x z) s := by
      rw [discreteSchemePointProjectedExtClass_sum]
    _ = _ := by
      dsimp only [schemeModuleExtSectionTracePairing,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
      rw [Ext.comp_sum,map_sum]
/-- For an ACTUAL Artinian original cut,finite point set and discrete
topology are DERIVED from native scheme instances. Only the original
morphism,coefficient and SAME global Ext class are inputs. -/
theorem artinianSchemePointProjectedExtClass_sum
    {D X : Scheme.{u}} [IsArtinianScheme D]
    (f : D ⟶ X) (L : D.Modules) {W : X.Modules} {r : ℕ}
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W r) :
    letI : Fintype D := Fintype.ofFinite D
    (∑ x : D,discreteSchemePointProjectedExtClass f L x z)=z := by
  letI : Fintype D := Fintype.ofFinite D
  exact discreteSchemePointProjectedExtClass_sum f L z
end LinearStudy
