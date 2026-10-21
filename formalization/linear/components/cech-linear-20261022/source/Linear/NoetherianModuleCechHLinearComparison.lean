module
public import Linear.NoetherianModuleCechHPointwiseNaturality
public import Linear.OrderedModuleCechCoefficientScalar
public import Linear.SchemeModuleActualHBaseScalars
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
attribute [local irreducible] noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso
  orderedModuleCechActualAbelianComplexIso noetherianFiniteOrderedAffineCover_actualHigherHIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- The SAME original module-Cech/native-positive-H comparison commutes
with ACTUAL base-global-section multiplication. Derived by specializing
coefficient naturality to the ORIGINAL coefficient scalar morphism. -/
theorem noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_smul
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (r : Γ(S,⊤))
    (x : (orderedBaseCechComplex π M U).homology (n+1)) :
    letI := schemeModuleActualHBaseModule π M (n+1)
    (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n).hom (r • x) =
      r • (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n).hom x := by
  letI := schemeModuleActualHBaseModule π M (n+1)
  rw [schemeModuleActualHBaseModule_smul]
  have h := noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_coefficient_naturality_apply
    π U hU haff (originalGlobalModuleScalar (π.appTop r) M) n x
  have hs := orderedBaseCechActualCoefficientMap_originalScalar π M r U
  have hh := congrArg (fun g : orderedBaseCechComplex π M U ⟶ orderedBaseCechComplex π M U =>
    HomologicalComplex.homologyMap g (n+1)) hs
  rw [actualHomologicalComplex_homologyMap_smul_id] at hh
  rw [hh] at h
  exact h
/-- The SAME pre-existing comparison upgraded to a LINEAR equivalence
for the intrinsic ORIGINAL base-scalar action. This does NOT define the
H scalar action by transporting it through this comparison. -/
def noetherianFiniteOrderedAffineCover_moduleCechActualHigherHLinearEquiv
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    letI := schemeModuleActualHBaseModule π M (n+1)
    (orderedBaseCechComplex π M U).homology (n+1) ≃ₗ[Γ(S,⊤)]
      schemeModuleActualCohomology X M (n+1) := by
  letI := schemeModuleActualHBaseModule π M (n+1)
  exact {
    (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n).addCommGroupIsoToAddEquiv with
    map_smul' := fun r x =>
      noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_smul π U hU haff M n r x }
/-- Exact equality of underlying maps with the OLD actual comparison. -/
theorem noetherianFiniteOrderedAffineCover_moduleCechActualHigherHLinearEquiv_apply
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : (orderedBaseCechComplex π M U).homology (n+1)) :
    noetherianFiniteOrderedAffineCover_moduleCechActualHigherHLinearEquiv π U hU haff M n x =
      (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n).hom x := rfl
end LinearStudy
