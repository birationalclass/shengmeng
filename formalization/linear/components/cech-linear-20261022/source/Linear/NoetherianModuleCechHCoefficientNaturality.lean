module
public import Linear.NoetherianModuleCechHFactorization
public import Linear.OrderedModuleCechActualCoefficientMap
public import Linear.OrderedModuleCechActualAbelianNaturality
public import Linear.ModuleHomologyForgettingNaturality
public import Linear.NoetherianOrderedCechHCoefficientNaturality
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
  orderedModuleCechActualAbelianHomologyIso
attribute [local irreducible] noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso
  orderedModuleCechActualAbelianComplexIso noetherianFiniteOrderedAffineCover_actualHigherHIso
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- The SAME original MODULE-valued Cech/native-positive-H comparison is
natural in ORIGINAL module coefficient maps. All local-H acyclicity is
DERIVED from the original Noetherian affine-intersection cover and BOTH
quasicoherent coefficients. No desired naturality or scalar premise. -/
theorem noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_coefficient_naturality
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap (orderedBaseCechActualCoefficientMap π f U) (n+1)) ≫
      (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff N n).hom =
    (noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso π U hU haff M n).hom ≫
      (CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) (n+1)).map
        ((schemeModuleToActualAbelianSheaf X).map f) := by
  have h₁ : CommSq
      ((forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap (orderedBaseCechActualCoefficientMap π f U) (n+1)))
      (orderedModuleCechActualAbelianHomologyIso π M U (n+1)).hom
      (orderedModuleCechActualAbelianHomologyIso π N U (n+1)).hom
      (HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f)) (n+1)) :=
    ⟨orderedModuleCechActualAbelianHomologyIso_coefficient_naturality π f U (n+1)⟩
  have h₂ : CommSq
      (HomologicalComplex.homologyMap
        (orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map f)) (n+1))
      (noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff M n).hom
      (noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff N n).hom
      ((CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) (n+1)).map
        ((schemeModuleToActualAbelianSheaf X).map f)) :=
    ⟨noetherianFiniteOrderedAffineCover_actualHigherHIso_coefficient_naturality X U hU haff f n⟩
  rw [noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_twoFactor,
    noetherianFiniteOrderedAffineCover_moduleCechActualHigherHIso_twoFactor]
  exact (h₁.vert_comp h₂).w
end LinearStudy
