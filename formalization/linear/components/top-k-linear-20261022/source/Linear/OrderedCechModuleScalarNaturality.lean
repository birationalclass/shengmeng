module
public import Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.SchemeModuleScalarNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- The old coefficient-iso hom is EXACTLY its original coefficient map. -/
theorem orderedTopAbelianCechCoefficientIso_hom_eq_map {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) :
    (orderedTopAbelianCechCoefficientIso U e).hom =
      orderedTopAbelianCechCoefficientMap X U e.hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl
/-- The inverse also retains the ORIGINAL coefficient map. -/
theorem orderedTopAbelianCechCoefficientIso_inv_eq_map {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) :
    (orderedTopAbelianCechCoefficientIso U e).inv =
      orderedTopAbelianCechCoefficientMap X U e.inv := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl
/-- EVERY original O-linear coefficient morphism commutes with the SAME
actual global scalar on its ORIGINAL ordered Cech complex. -/
theorem orderedTopAbelianCech_moduleScalar_naturality {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (r : Γ(X,⊤)) {M N : X.Modules} (f : M ⟶ N) :
    orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f) ≫
      orderedTopAbelianCechCoefficientMap X U
        ((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r N)) =
    orderedTopAbelianCechCoefficientMap X U
        ((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r M)) ≫
      orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f) := by
  let C := schemeModuleToActualAbelianSheaf X ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u} ⋙ orderedFormalCechCoefficientFunctor U
  change C.map f ≫ C.map (originalGlobalModuleScalar r N) =
    C.map (originalGlobalModuleScalar r M) ≫ C.map f
  simpa only [Functor.map_comp] using
    congrArg C.map (originalGlobalModuleScalar_naturality r f).symm
end LinearStudy
