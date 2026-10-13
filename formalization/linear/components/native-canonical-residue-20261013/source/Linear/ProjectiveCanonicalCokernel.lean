module
public import Linear.ProjectiveCanonicalResidueKernel
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

/-- The kernel of the actual canonical residue is exactly the image of the
actual previous Cech differential; no exactness hypothesis is supplied. -/
theorem coordinateCanonicalResidue_ker_eq_range (n : ℕ)
    (hc : Fintype.card σ = n+2) :
    LinearMap.ker (coordinateCanonicalResidue (R := R) (n+1) hc) =
      LinearMap.range (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n).hom := by
  ext s
  constructor
  · intro hs
    exact exists_preimage_coordinateCanonicalResidue_zero n hc s hs
  · rintro ⟨t,rfl⟩
    exact coordinateCanonicalResidue_boundary n hc t

/-- The actual top Cech quotient for degree -(r+1) is one copy of the
coefficient ring. In positive dimension it is top cohomology, since all
top cochains have already been proved to be cycles. -/
def coordinateCanonicalCokernelEquiv (n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) (n+1) ⧸
      LinearMap.range (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n).hom) ≃ₗ[coordinateCanonicalBaseRing R]
      coordinateCanonicalBaseRing R :=
  (Submodule.quotEquivOfEq _ _ (coordinateCanonicalResidue_ker_eq_range n hc).symm).trans
    ((coordinateCanonicalResidue (R := R) (n+1) hc).quotKerEquivOfSurjective
      (coordinateCanonicalResidue_surjective (n+1) hc))

/-- The induced quotient isomorphism sends the class of an actual cochain
to its canonical Laurent coefficient. -/
theorem coordinateCanonicalCokernelEquiv_apply_mk (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) (n+1)) :
    coordinateCanonicalCokernelEquiv (R := R) n hc (Submodule.Quotient.mk s) =
      coordinateCanonicalResidue (R := R) (n+1) hc s := by
  simp [coordinateCanonicalCokernelEquiv]
end MvPolynomial
