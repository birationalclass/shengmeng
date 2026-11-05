module
public import Linear.OrderedCechActualHComparison
public import Linear.OrderedModuleCechActualAbelian
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
/-- Actual ordered Cech homology computes SAME native H for ANY QC module
on a finite affine-intersection cover of a locally Noetherian scheme.
Local native-H acyclicity is DERIVED;no Cech exactness or comparison premise. -/
def noetherianFiniteOrderedAffineCover_actualHigherHIso (X : Scheme.{u})
    [IsLocallyNoetherian X] {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (orderedTopAbelianCechComplex X U ((schemeModuleToActualAbelianSheaf X).obj M)).homology (n+1) ≅
      AddCommGrpCat.of (schemeModuleActualCohomology X M (n+1)) :=
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic X U hU
    ((schemeModuleToActualAbelianSheaf X).obj M)
    (fun p a j => noetherianAffineOpen_quasicoherent_actualHigherH_vanish X _ (haff p a) M j) n
/-- SAME original module-valued ordered Cech homology computes SAME actual
native H after forgetting base scalars. Forgetting scalars preserves native
homology;all original complex differentials and alternating signs are retained.
No chosen comparison,local-H or desired global-H certificate is added. -/
def noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (pi : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).obj
      ((orderedBaseCechComplex pi M U).homology (n+1)) ≅
        AddCommGrpCat.of (schemeModuleActualCohomology X M (n+1)) := by
  let H := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  let C := orderedBaseCechComplex pi M U
  exact ((C.sc (n+1)).mapHomologyIso H).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (n+1)).mapIso (orderedModuleCechActualAbelianComplexIso pi M U) ≪≫
      noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff M n
end LinearStudy
