module
public import Linear.InjectiveClosedClassExtAcyclic
public import Linear.TopAbelianSheafFlasqueShortExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian TopologicalSpace
universe u
/-- Every actual flasque abelian SHEAF has zero positive native SHEAF cohomology.
The native source is the constant integer SHEAF on the same original space. -/
theorem topAbelianSheaf_flasque_higherCohomology_vanish (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : TopCat.Sheaf.IsFlasque F) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F (n+1)) :=
  ext_subsingleton_of_injective_closed_class
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (fun M => TopCat.Sheaf.IsFlasque M)
    (fun hS hP hI => topAbelianSheaf_flasque_quotient_of_injective hS hP hI)
    (fun hS hP a => topAbelianSheaf_shortExact_integerHom_lift_of_flasque hS hP a) F hF n
end LinearStudy
