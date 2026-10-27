module
public import Linear.OrderedCechNativeHVanishing
public import Linear.NoetherianAffineOpenActualCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
universe u
/-- On ANY locally Noetherian scheme,original finite ORDERED affine intersections
and SAME ordered Cech acyclicity imply actual native SHEAF-H vanishing for ANY QC
module.Local acyclicity is DERIVED from affineness and Noetherianity. -/
theorem noetherianFiniteOrderedAffineCover_actualHigherH_vanish (X : Scheme.{u})
    [IsLocallyNoetherian X] {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ (p : ℕ) (a : OrderedCechIndex ι p),IsAffineOpen (∏ᶜ fun k : Fin (p+1) => U (a.1 k)))
    (M : X.Modules) [M.IsQuasicoherent]
    (hC : ∀ p,(orderedTopAbelianCechComplex X U ((schemeModuleToActualAbelianSheaf X).obj M)).ExactAt (p+1))
    (n : ℕ) : Subsingleton (schemeModuleActualCohomology X M (n+1)) :=
  topFiniteOrderedCech_actualHigherH_vanish_of_localAcyclic X U hU
    ((schemeModuleToActualAbelianSheaf X).obj M) hC
    (fun p a j => noetherianAffineOpen_quasicoherent_actualHigherH_vanish X _ (haff p a) M j) n
end LinearStudy
