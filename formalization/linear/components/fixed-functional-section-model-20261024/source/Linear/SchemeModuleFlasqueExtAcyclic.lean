module
public import Linear.InjectiveClosedClassExtAcyclic
public import Linear.SchemeModuleFlasqueShortExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- Actual flasque module sheaves have no positive GLOBAL Ext from the structure sheaf.
This is neither derived internal sheaf Ext nor the still-open cohomology comparison. -/
theorem schemeModule_flasque_relativeExt_vanish (X : Scheme.{u}) (F : X.Modules)
    (hF : TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj F)) (n : ℕ) :
    Subsingleton (Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F (n+1)) :=
  ext_subsingleton_of_injective_closed_class (SheafOfModules.unit X.ringCatSheaf)
    (fun M => TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj M))
    (fun hS hP hI => schemeModule_flasque_quotient_of_injective hS hP hI)
    (fun hS hP f => schemeModule_shortExact_unitHom_lift_of_flasque hS hP f) F hF n
end LinearStudy
