module
public import Linear.NoetherianOrderedAffineCoverActualHComparison
public import Linear.OrderedModuleCechActualAbelianHomology
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
/-- Exact factorization of the SAME original module-Cech/native-H comparison.
Only names the existing construction;no replacement comparison is introduced. -/
theorem noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_factorization
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n =
      (((orderedBaseCechComplex π M U).sc (n+1)).mapHomologyIso
        (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u})).symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ (n+1)).mapIso
        (orderedModuleCechActualAbelianComplexIso π M U) ≪≫
      noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff M n := by
  rfl
/-- The SAME old actual-H comparison factors through the named original
two-factor forgetting comparison;this is an exact equality. -/
theorem noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_twoFactor
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n =
      orderedModuleCechActualAbelianHomologyIso π M U (n+1) ≪≫
        noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff M n := by
  rw [noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_factorization]
  apply Iso.ext
  simp only [orderedModuleCechActualAbelianHomologyIso,Iso.trans_hom,Iso.symm_hom,Category.assoc]
end LinearStudy
