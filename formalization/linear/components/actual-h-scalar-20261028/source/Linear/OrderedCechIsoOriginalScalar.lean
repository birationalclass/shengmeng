module
public import Linear.OrderedCechModuleScalarNaturality
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
/-- Original scalar naturality for the hom of ANY O-linear coefficient iso. -/
theorem orderedTopAbelianCechCoefficientIso_moduleScalar_hom {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (r : Γ(X,⊤))
    {M N : X.Modules} (e : M ≅ N) :
    orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r M)) ≫
      (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf X).mapIso e)).hom =
    (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf X).mapIso e)).hom ≫
      orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r N)) := by
  rw [orderedTopAbelianCechCoefficientIso_hom_eq_map]
  exact (orderedTopAbelianCech_moduleScalar_naturality U r e.hom).symm
/-- Original scalar naturality for the inverse of ANY O-linear coefficient iso. -/
theorem orderedTopAbelianCechCoefficientIso_moduleScalar_inv {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (r : Γ(X,⊤))
    {M N : X.Modules} (e : M ≅ N) :
    orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r N)) ≫
      (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf X).mapIso e)).inv =
    (orderedTopAbelianCechCoefficientIso U ((schemeModuleToActualAbelianSheaf X).mapIso e)).inv ≫
      orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r M)) := by
  rw [orderedTopAbelianCechCoefficientIso_inv_eq_map]
  exact (orderedTopAbelianCech_moduleScalar_naturality U r e.inv).symm
end LinearStudy
