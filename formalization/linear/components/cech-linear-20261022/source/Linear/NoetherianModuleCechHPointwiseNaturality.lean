module
public import Linear.NoetherianModuleCechHCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option diagnostics true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] orderedBaseCechActualCoefficientMap
attribute [local irreducible] noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso
  orderedModuleCechActualAbelianComplexIso noetherianFiniteOrderedAffineCover_actualHigherHIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- Pointwise form of SAME original module-Cech/native-H coefficient
naturality,with native homologyMap and native H.map in the statement. -/
theorem noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_coefficient_naturality_apply
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ)
    (x : (orderedBaseCechComplex π M U).homology (n+1)) :
    (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff N n).hom
        (HomologicalComplex.homologyMap (orderedBaseCechActualCoefficientMap π f U) (n+1) x) =
      CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) (n+1)
        ((noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n).hom x) :=
  ConcreteCategory.congr_hom
    (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_coefficient_naturality
      π U hU haff f n) x
end LinearStudy
