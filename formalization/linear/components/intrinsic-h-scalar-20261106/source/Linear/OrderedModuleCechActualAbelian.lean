module
public import Linear.FormalProductEvaluationWhiskering
public import Linear.NoetherianOrderedAffineCoverNativeH
public import Mathlib.Algebra.Category.ModuleCat.Abelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Forgetting the base scalar ring leaves the SAME original abelian presheaf. -/
def baseModulePresheafActualAbelianIso {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    baseModulePresheaf π M ⋙ forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u} ≅
      ((schemeModuleToActualAbelianSheaf X).obj M).obj := Iso.refl _
/-- The SAME original module-valued ordered Cech complex is the actual ordered
abelian-sheaf Cech complex after forgetting base scalars,including all signs. -/
def orderedModuleCechActualAbelianComplexIso {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
      (orderedBaseCechComplex π M U) ≅
        orderedTopAbelianCechComplex X U ((schemeModuleToActualAbelianSheaf X).obj M) := by
  let T := baseModulePresheaf π M
  let H := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  let F := (FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} Γ(S,⊤))).obj T
  let e : orderedBaseCechComplex π M U ≅ orderedFormalCechComplex F U := Iso.refl _
  exact (H.mapHomologicalComplex (.up ℕ)).mapIso e ≪≫
    orderedFormalCechWhiskeringIso U F H ≪≫
      orderedFormalCechComplexIso U (formalProductEvaluationWhiskeringIso T H ≪≫
        (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).mapIso
          (baseModulePresheafActualAbelianIso π M))
/-- The actual ORIGINAL module-valued ordered Cech vanishing now implies SAME
native SHEAF-H vanishing,on a finite affine-intersection cover of a locally
Noetherian scheme.No ordered/full,local-H or desired global-H premise. -/
theorem noetherianFiniteOrderedAffineCover_actualHigherH_vanish_of_moduleCechExact
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent]
    (hC : ∀ p,(orderedBaseCechComplex π M U).ExactAt (p+1))
    (n : ℕ) : Subsingleton (schemeModuleActualCohomology X M (n+1)) := by
  apply noetherianFiniteOrderedAffineCover_actualHigherH_vanish X U hU haff M
  intro p
  let H := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  have hE : ((H.mapHomologicalComplex (.up ℕ)).obj
      (orderedBaseCechComplex π M U)).ExactAt (p+1) :=
    ShortComplex.Exact.map (hC p) H
  exact hE.of_iso (orderedModuleCechActualAbelianComplexIso π M U)
end LinearStudy
