module
public import Linear.OrderedModuleCechActualAbelianNaturality
public import Linear.OrderedModuleCechCoefficientScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Name the SAME original coefficient complex map with its original
source/target complex types EXPLICIT. No replacement map is chosen. -/
def orderedBaseCechActualCoefficientMap {X S : Scheme.{u}} (π : X ⟶ S)
    {M N : X.Modules} (f : M ⟶ N) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedBaseCechComplex π M U ⟶ orderedBaseCechComplex π N U :=
  (orderedBaseCechComplexFunctor π U).map f
/-- Exact agreement with the existing original complex functor map. -/
theorem orderedBaseCechActualCoefficientMap_eq_functorMap {X S : Scheme.{u}} (π : X ⟶ S)
    {M N : X.Modules} (f : M ⟶ N) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedBaseCechActualCoefficientMap π f U = (orderedBaseCechComplexFunctor π U).map f := rfl
/-- Exact original forgetting square through the small named map. -/
theorem orderedBaseCechActualCoefficientMap_forgetting_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map
        (orderedBaseCechActualCoefficientMap π f U) ≫
      (orderedModuleCechActualAbelianComplexIso π N U).hom =
    (orderedModuleCechActualAbelianComplexIso π M U).hom ≫
      orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f) :=
  orderedModuleCechActualAbelianComplexIso_coefficient_naturality π f U
/-- Original scalar coefficient map has the SAME native scalar-identity value. -/
theorem orderedBaseCechActualCoefficientMap_originalScalar
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (r : Γ(S,⊤))
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedBaseCechActualCoefficientMap π (originalGlobalModuleScalar (π.appTop r) M) U =
      r • 𝟙 (orderedBaseCechComplex π M U) :=
  orderedBaseCechComplexFunctor_map_originalScalar π M r U
end LinearStudy
