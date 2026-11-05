module
public import Linear.OrderedModuleCechActualAbelian
public import Linear.ModuleOrderedBaseCechFunctor
public import Linear.OrderedFormalCechCoefficientFunctor
public import Linear.FormalProductCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- The ORIGINAL base-linear Cech coefficient map equals the SAME
formal-presheaf coefficient map,including its actual alternating differential. -/
theorem orderedBaseCechComplexFunctor_map_eq_formal
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {M N : X.Modules} (f : M ⟶ N) :
    (orderedBaseCechComplexFunctor π U).map f =
      (orderedFormalCechCoefficientFunctor U).map
        ((FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))).map
          ((baseModulePresheafFunctor π).map f)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl
/-- Forgetting original base scalar structure commutes with the SAME
original module coefficient map on every open. -/
theorem baseModulePresheafActualAbelianIso_coefficient_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N) :
    Functor.whiskerRight ((baseModulePresheafFunctor π).map f)
        (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}) ≫
      (baseModulePresheafActualAbelianIso π N).hom =
    (baseModulePresheafActualAbelianIso π M).hom ≫
      ((schemeModuleToActualAbelianSheaf X).map f).hom := by
  ext U
  rfl
/-- Name the SAME two original formal-presheaf forgetting factors used
inside the existing module-Cech/abelian-Cech comparison. -/
def orderedBaseModuleActualAbelianCoefficientIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    (FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))).obj
        (baseModulePresheaf π M) ⋙ forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u} ≅
      (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).obj
        (((schemeModuleToActualAbelianSheaf X).obj M).obj) :=
  formalProductEvaluationWhiskeringIso (baseModulePresheaf π M)
      (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}) ≪≫
    (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).mapIso
      (baseModulePresheafActualAbelianIso π M)
/-- Coefficient naturality of the SAME two original presheaf factors,
derived from native product projections and original open-section maps. -/
theorem orderedBaseModuleActualAbelianCoefficientIso_coefficient_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N) :
    Functor.whiskerRight
        ((FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))).map
          ((baseModulePresheafFunctor π).map f))
        (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}) ≫
      (orderedBaseModuleActualAbelianCoefficientIso π N).hom =
    (orderedBaseModuleActualAbelianCoefficientIso π M).hom ≫
      (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).map
        (((schemeModuleToActualAbelianSheaf X).map f).hom) := by
  let H := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  let E := FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}
  let a := (baseModulePresheafFunctor π).map f
  have h₁ : CommSq
      (Functor.whiskerRight ((FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))).map a) H)
      (formalProductEvaluationWhiskeringIso (baseModulePresheaf π M) H).hom
      (formalProductEvaluationWhiskeringIso (baseModulePresheaf π N) H).hom
      (E.map (Functor.whiskerRight a H)) :=
    ⟨formalProductEvaluationWhiskeringIso_coefficient_naturality a H⟩
  have h₂ : CommSq (E.map (Functor.whiskerRight a H))
      (E.mapIso (baseModulePresheafActualAbelianIso π M)).hom
      (E.mapIso (baseModulePresheafActualAbelianIso π N)).hom
      (E.map (((schemeModuleToActualAbelianSheaf X).map f).hom)) := by
    constructor
    change E.map _ ≫ E.map _ = E.map _ ≫ E.map _
    simpa only [Functor.map_comp] using
      congrArg E.map (baseModulePresheafActualAbelianIso_coefficient_naturality π f)
  exact (h₁.vert_comp h₂).w
end LinearStudy
