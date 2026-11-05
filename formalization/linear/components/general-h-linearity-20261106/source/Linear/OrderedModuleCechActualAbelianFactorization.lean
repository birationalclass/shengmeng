module
public import Linear.OrderedModuleCechCoefficientFactors
public import Linear.OrderedFormalCechWhiskeringNaturality
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
/-- Exact factorization of the SAME pre-existing original module-Cech /
abelian-Cech comparison,not a replacement complex or comparison map. -/
theorem orderedModuleCechActualAbelianComplexIso_factorization
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedModuleCechActualAbelianComplexIso π M U =
      ((forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).mapIso
        (Iso.refl (orderedBaseCechComplex π M U)) ≪≫
      orderedFormalCechWhiskeringIso U
        ((FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))).obj (baseModulePresheaf π M))
        (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}) ≪≫
      (orderedFormalCechCoefficientFunctor (D:=AddCommGrpCat.{u}) U).mapIso
        (orderedBaseModuleActualAbelianCoefficientIso π M) := by
  rw [orderedFormalCechCoefficientFunctor_mapIso]
  unfold orderedModuleCechActualAbelianComplexIso orderedBaseModuleActualAbelianCoefficientIso
  rfl
end LinearStudy
