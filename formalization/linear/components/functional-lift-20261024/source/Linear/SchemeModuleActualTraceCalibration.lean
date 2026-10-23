module
public import Linear.SchemeModuleExtTracePairing
public import Linear.SchemeModuleActualCohomologyGroup
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
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
/-- Convert an ORIGINAL actual-H trace to the SAME GLOBAL unit-Ext trace
using the canonical calibrated comparison. This is an additive construction,
not a geometric normalization or a new dualizing identification. -/
def schemeModuleActualHToGlobalExtTrace
    (trace : schemeModuleActualCohomology X W r →+ R) :
    Ext.{u} (SheafOfModules.unit X.ringCatSheaf) W r →+ R :=
  trace.comp (schemeModuleGlobalExtActualHAddEquiv X W r).toAddMonoidHom
/-- The ORIGINAL Yoneda/Ext pairing is EXACTLY the ORIGINAL actual-H
coefficient map followed by trace. Calibrated coefficient naturality is
reused;no desired pairing compatibility square is an input. -/
theorem schemeModuleActualHToGlobalExtTrace_pairing
    (trace : schemeModuleActualCohomology X W r →+ R) (a : M ⟶ W)
    (h : schemeModuleActualCohomology X M r) :
    schemeModuleActualHTracePairing (schemeModuleActualHToGlobalExtTrace trace) a h =
      trace (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map a) r h) := by
  change trace (schemeModuleGlobalExtActualHAddEquiv X W r
    (((schemeModuleGlobalExtActualHAddEquiv X M r).symm h).comp
      (Ext.mk₀ a) (add_zero r))) = _
  rw [schemeModuleGlobalExtActualHAddEquiv_naturality,AddEquiv.apply_symm_apply]
/-- The SAME original chain/Koszul section boundary satisfies the actual-H
trace formula after replacing the EXPLICIT unit-Ext trace by the calibrated
trace constructed from actual H. No replacement boundary or Ext roof. -/
theorem schemeModuleOriginalActualSectionBoundary_actualH_trace_transpose
    (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (C.X (r+1))) (phi : C.X r ≅ M)
    (a : M ⟶ W) (trace : schemeModuleActualCohomology X W r →+ R)
    (s : Γ(E,⊤)) :
    trace (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map a) r
      (schemeModuleOriginalActualSectionBoundary C r alpha hAlpha hAbove phi s)) =
    schemeModuleExtSectionTracePairing (schemeModuleActualHToGlobalExtTrace trace)
      (schemeModuleExtClassCoefficientPushforwardAddHom
        (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha phi.hom
          (hAbove.eq_of_src _ _)) a) s := by
  rw [← schemeModuleActualHToGlobalExtTrace_pairing]
  exact schemeModuleOriginalActualSectionBoundary_trace_transpose
    C r alpha hAlpha hAbove phi a (schemeModuleActualHToGlobalExtTrace trace) s
end LinearStudy
