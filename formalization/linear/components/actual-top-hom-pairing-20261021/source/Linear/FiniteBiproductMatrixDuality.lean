module
public import Linear.FiniteBiproductDualCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [CommRing R] {I J : Type} [Fintype I] [Fintype J]
variable (f : I → ModuleCat R) (g : J → ModuleCat R)

/-- Put the ACTUAL original categorical map u into its original tuple
coordinates,using the chosen mathlib biproduct comparison. -/
def finiteBiproductMapCoordinates (u : (⨁ f) ⟶ ⨁ g) :
    (∀ i, f i) →ₗ[R] (∀ j, g j) :=
  ((ModuleCat.biproductIsoPi f).inv ≫ u ≫ (ModuleCat.biproductIsoPi g).hom).hom

variable [DecidableEq I]

/-- The actual coordinate entry is the ORIGINAL categorical component
of u. No component/matrix equality is an input. -/
theorem finiteBiproductMapCoordinates_single (u : (⨁ f) ⟶ ⨁ g)
    (i : I) (j : J) (x : f i) :
    finiteBiproductMapCoordinates f g u (Pi.single i x) j =
      (biproduct.components u i j) x := by
  have hinv : (ModuleCat.biproductIsoPi f).inv (Pi.single i x) =
      (biproduct.ι f i) x := by
    rw [← finiteBiproductCoordinate_ι f i x]
    change (ModuleCat.biproductIsoPi f).toLinearEquiv.symm
      ((ModuleCat.biproductIsoPi f).toLinearEquiv ((biproduct.ι f i) x)) = _
    exact (ModuleCat.biproductIsoPi f).toLinearEquiv.symm_apply_apply _
  change ((ModuleCat.biproductIsoPi g).hom
    (u ((ModuleCat.biproductIsoPi f).inv (Pi.single i x)))) j = _
  rw [hinv,finiteBiproductCoordinate_apply]
  rfl

variable [DecidableEq J]

/-- The matrix of the duals of the ORIGINAL entries of an ARBITRARY
actual categorical map u agrees with its actual tuple dual map under
canonical finite dual assembly. No dimension or comparison is assumed. -/
theorem finiteBiproductActualMap_dual_matrix (u : (⨁ f) ⟶ ⨁ g) :
    biproduct.matrix (fun j i => ModuleCat.ofHom (biproduct.components u i j).hom.dualMap) ≫
      (finiteBiproductDualIso f).hom =
    (finiteBiproductDualIso g).hom ≫ ModuleCat.ofHom (finiteBiproductMapCoordinates f g u).dualMap := by
  apply biproduct.hom_ext'
  intro j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.pi_ext
  intro i x
  change (finiteBiproductDualIso f).hom
    ((biproduct.matrix (fun j i => ModuleCat.ofHom (biproduct.components u i j).hom.dualMap))
      ((biproduct.ι (fun j => ModuleCat.of R (Module.Dual R (g j))) j) φ)) (Pi.single i x) =
    (finiteBiproductDualIso g).hom
      ((biproduct.ι (fun j => ModuleCat.of R (Module.Dual R (g j))) j) φ)
        (finiteBiproductMapCoordinates f g u (Pi.single i x))
  rw [finiteBiproductDualIso_ι_apply,finiteBiproductMapCoordinates_single]
  change finitePiDualEquiv (fun i => f i)
    ((ModuleCat.biproductIsoPi (fun i => ModuleCat.of R (Module.Dual R (f i)))).hom
      ((biproduct.matrix (fun j i => ModuleCat.ofHom (biproduct.components u i j).hom.dualMap))
        ((biproduct.ι (fun j => ModuleCat.of R (Module.Dual R (g j))) j) φ))) (Pi.single i x) =
    φ ((biproduct.components u i j) x)
  rw [finitePiDualEquiv_single,finiteBiproductCoordinate_apply]
  change ((biproduct.ι (fun j => ModuleCat.of R (Module.Dual R (g j))) j ≫
    biproduct.matrix (fun j i => ModuleCat.ofHom (biproduct.components u i j).hom.dualMap) ≫
      biproduct.π (fun i => ModuleCat.of R (Module.Dual R (f i))) i) φ) x = _
  rw [biproduct.ι_matrix_assoc,biproduct.lift_π]
  rfl

end LinearStudy
