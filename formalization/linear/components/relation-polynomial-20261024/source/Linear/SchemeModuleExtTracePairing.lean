module
public import Linear.SchemeModuleOriginalActualSectionBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u v
variable {X : Scheme.{u}} {E M W : X.Modules} {r : ℕ}
variable {R : Type v} [AddCommGroup R]
/-- Actual native H paired with a coefficient morphism by SAME calibrated
Ext/H inverse and Yoneda composition followed by an EXPLICIT trace.
This constructs an additive pairing;no trace existence,perfection,
canonical dualizing identification or geometric Serre duality is assumed proved. -/
def schemeModuleActualHTracePairing
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ R)
    (a : M ⟶ W) : schemeModuleActualCohomology X M r →+ R where
  toFun h := trace (((schemeModuleGlobalExtActualHAddEquiv X M r).symm h).comp
    (Ext.mk₀ a) (add_zero r))
  map_zero' := by simp only [map_zero,Ext.zero_comp]
  map_add' h k := by simp only [map_add,Ext.add_comp]
/-- Actual global-section/Ext pairing induced by SAME explicit trace.
This uses the original unit-Hom/global-section equivalence. -/
def schemeModuleExtSectionTracePairing
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ R)
    (z : Ext.{u} E W r) : Γ(E,⊤) →+ R where
  toFun s := trace ((Ext.mk₀ ((schemeModuleUnitHomGlobalSectionsAddEquiv X E).symm s)).comp
    z (zero_add r))
  map_zero' := by simp only [map_zero,Ext.mk₀_zero,Ext.zero_comp]
  map_add' s t := by simp only [map_add,Ext.mk₀_add,Ext.add_comp]
/-- Push the SAME Ext class forward by an ACTUAL coefficient morphism. -/
def schemeModuleExtClassCoefficientPushforwardAddHom (epsilon : Ext.{u} E M r) :
    (M ⟶ W) →+ Ext.{u} E W r where
  toFun a := epsilon.comp (Ext.mk₀ a) (add_zero r)
  map_zero' := by simp only [Ext.mk₀_zero,Ext.comp_zero]
  map_add' a b := by simp only [Ext.mk₀_add,Ext.comp_add]
/-- Transpose FORMULA for actual section boundary,derived from Yoneda
associativity rather than inserted as a compatibility hypothesis.
The trace remains EXPLICIT;its geometric existence/perfection is separate. -/
theorem schemeModuleExtClassActualSectionBoundary_trace_transpose
    (epsilon : Ext.{u} E M r) (a : M ⟶ W)
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ R)
    (s : Γ(E,⊤)) :
    schemeModuleActualHTracePairing trace a (schemeModuleExtClassActualSectionBoundary epsilon s) =
      schemeModuleExtSectionTracePairing trace
        (schemeModuleExtClassCoefficientPushforwardAddHom epsilon a) s := by
  dsimp only [schemeModuleActualHTracePairing,schemeModuleExtClassActualSectionBoundary,
    schemeModuleExtSectionTracePairing,schemeModuleExtClassCoefficientPushforwardAddHom,
    AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [AddEquiv.symm_apply_apply]
  congr 1
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add r)
/-- Same transpose formula for SAME original chain/Koszul Ext roof and
SAME actual endpoint morphism. No replacement Ext class is introduced. -/
theorem schemeModuleOriginalActualSectionBoundary_trace_transpose
    (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (C.X (r+1))) (phi : C.X r ≅ M)
    (a : M ⟶ W)
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ R)
    (s : Γ(E,⊤)) :
    schemeModuleActualHTracePairing trace a
        (schemeModuleOriginalActualSectionBoundary C r alpha hAlpha hAbove phi s) =
      schemeModuleExtSectionTracePairing trace
        (schemeModuleExtClassCoefficientPushforwardAddHom
          (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
            (hAbove.eq_of_src _ _)) a) s := by
  exact schemeModuleExtClassActualSectionBoundary_trace_transpose _ a trace s
/-- CONDITIONAL consequence of explicit trace NONDEGENERACY and actual
boundary surjectivity:coefficient pushforward is injective.
No actual geometric perfect pairing,trace or dualizing object is supplied
by this theorem;these hypotheses must be discharged independently. -/
theorem schemeModuleExtClassCoefficientPushforward_injective_of_trace
    (epsilon : Ext.{u} E M r)
    (trace : Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ R)
    (hTrace : ∀ a : M ⟶ W,(∀ h : schemeModuleActualCohomology X M r,
      schemeModuleActualHTracePairing trace a h = 0) → a = 0)
    (hDelta : Function.Surjective (schemeModuleExtClassActualSectionBoundary epsilon)) :
    Function.Injective (schemeModuleExtClassCoefficientPushforwardAddHom (W := W) epsilon) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hTrace (a-b)
  intro h
  obtain ⟨s,rfl⟩ := hDelta h
  rw [schemeModuleExtClassActualSectionBoundary_trace_transpose]
  have hz : schemeModuleExtClassCoefficientPushforwardAddHom epsilon (a-b) = 0 := by
    rw [map_sub,hab,sub_self]
  rw [hz]
  simp only [schemeModuleExtSectionTracePairing,Ext.comp_zero,map_zero,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
end LinearStudy
