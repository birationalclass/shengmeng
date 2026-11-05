module
public import Linear.AdditiveFunctorEndRingHom
public import Linear.OriginalGlobalModuleScalarRingHom
public import Linear.SchemeModuleActualCohomologyGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
/-- The native sheaf-H functor after forgetting ORIGINAL module coefficients.
This retains the existing cohomology groups and original coefficient maps. -/
def schemeModuleActualHFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  schemeModuleToAdditiveSheaf X ⋙ CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) n
instance schemeModuleActualHFunctor_additive (X : Scheme.{u}) (n : ℕ) :
    (schemeModuleActualHFunctor X n).Additive := by
  change (SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) n).Additive
  infer_instance
/-- Intrinsic ORIGINAL-global-section action on native actual H: apply the
native additive H functor to ACTUAL coefficient multiplication. No duality
comparison, arbitrary isomorphism, trace or scalar-compatibility premise. -/
def schemeModuleActualHScalarRingHom (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    Γ(X,⊤) →+* AddMonoid.End (schemeModuleActualCohomology X M n) :=
  (addCommGroupEndRingHom ((schemeModuleActualHFunctor X n).obj M)).comp
    ((additiveFunctorEndRingHom (schemeModuleActualHFunctor X n) M).comp
      (originalGlobalModuleScalarRingHom M))
/-- Exact calibration with the ORIGINAL coefficient multiplication map,
in EVERY cohomological degree on the SAME original space. -/
theorem schemeModuleActualHScalarRingHom_apply (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (r : Γ(X,⊤)) (x : schemeModuleActualCohomology X M n) :
    schemeModuleActualHScalarRingHom X M n r x =
      CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map
        (originalGlobalModuleScalar r M)) n x := rfl
end LinearStudy
