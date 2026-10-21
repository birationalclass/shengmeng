module
public import Linear.OrderedModuleCechActualCoefficientMap
public import Linear.ModuleHomologyForgettingNaturality
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
/-- Name the SAME two native module-homology/abelian-Cech-homology factors
already used inside the old actual-H comparison. No new cohomology model. -/
def orderedModuleCechActualAbelianHomologyIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).obj
        ((orderedBaseCechComplex π M U).homology n) ≅
      (orderedTopAbelianCechComplex X U ((schemeModuleToActualAbelianSheaf X).obj M)).homology n :=
  (((orderedBaseCechComplex π M U).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u})).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (orderedModuleCechActualAbelianComplexIso π M U)
/-- Naturality of the SAME two original forgetting/homology factors,
separately checked before composing with the derived actual-H comparison. -/
theorem orderedModuleCechActualAbelianHomologyIso_coefficient_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap (orderedBaseCechActualCoefficientMap π f U) n) ≫
      (orderedModuleCechActualAbelianHomologyIso π N U n).hom =
    (orderedModuleCechActualAbelianHomologyIso π M U n).hom ≫
      HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f)) n := by
  let H := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  let HC := H.mapHomologicalComplex (.up ℕ)
  let T := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) n
  let φ := orderedBaseCechActualCoefficientMap π f U
  let dM := ((orderedBaseCechComplex π M U).sc n).mapHomologyIso H
  let dN := ((orderedBaseCechComplex π N U).sc n).mapHomologyIso H
  let eM := orderedModuleCechActualAbelianComplexIso π M U
  let eN := orderedModuleCechActualAbelianComplexIso π N U
  let a := orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f)
  have h₁ : CommSq (H.map (HomologicalComplex.homologyMap φ n)) dM.inv dN.inv
      (HomologicalComplex.homologyMap (HC.map φ) n) :=
    ⟨moduleHomologyForgettingIso_coefficient_naturality φ n⟩
  have hc : CommSq (HC.map φ) eM.hom eN.hom a :=
    ⟨orderedBaseCechActualCoefficientMap_forgetting_naturality π f U⟩
  have h₂ : CommSq (HomologicalComplex.homologyMap (HC.map φ) n)
      (T.mapIso eM).hom (T.mapIso eN).hom (HomologicalComplex.homologyMap a n) :=
    T.map_commSq hc
  change H.map (HomologicalComplex.homologyMap φ n) ≫ (dN.inv ≫ (T.mapIso eN).hom) =
    (dM.inv ≫ (T.mapIso eM).hom) ≫ HomologicalComplex.homologyMap a n
  exact (h₁.vert_comp h₂).w
end LinearStudy
