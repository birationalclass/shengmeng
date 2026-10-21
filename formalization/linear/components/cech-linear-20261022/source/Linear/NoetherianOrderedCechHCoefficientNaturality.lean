module
public import Linear.OrderedCechActualHCoefficientNaturality
public import Linear.NoetherianOrderedAffineCoverActualHComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- SAME existing affine-QC ordered-Cech/native-H comparison is natural
in actual module morphisms. BOTH coefficient local acyclicity conditions
are DERIVED from the original Noetherian affine cover,not assumed. -/
theorem noetherianFiniteOrderedAffineCover_actualHigherHIso_coefficient_naturality
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (b : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (b.1 k)))
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
      (orderedTopAbelianCechCoefficientMap X U ((schemeModuleToActualAbelianSheaf X).map a)) (n+1) ≫
        (noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff N n).hom =
      (noetherianFiniteOrderedAffineCover_actualHigherHIso X U hU haff M n).hom ≫
        (CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) (n+1)).map ((schemeModuleToActualAbelianSheaf X).map a) :=
  topFiniteOrderedCech_actualHigherHIso_of_localAcyclic_coefficient_naturality X U hU
    ((schemeModuleToActualAbelianSheaf X).map a)
    (fun p b j => noetherianAffineOpen_quasicoherent_actualHigherH_vanish X _ (haff p b) M j)
    (fun p b j => noetherianAffineOpen_quasicoherent_actualHigherH_vanish X _ (haff p b) N j) n
end LinearStudy
