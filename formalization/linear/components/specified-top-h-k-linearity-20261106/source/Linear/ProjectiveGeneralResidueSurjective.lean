module
public import Linear.ProjectiveGeneralResidueCoordinates
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

def coordinateGeneralTopWeightCochain (m n : ℕ) (hc : Fintype.card σ = n+1)
    (e : ProjectiveNegativeWeight σ m) (r : coordinateCanonicalBaseRing R) :
    LinearStudy.OrderedCechSupportCochain (coordinateCanonicalBaseRing R)
      e.1.liftedNegativeSupport n :=
  ⟨fun _ => r, fun a ha => by
    have he := LinearStudy.orderedCechIndex_eq_full n (by simpa using hc) a
    rw [he,LinearStudy.orderedCechFullIndex_range] at ha
    exact False.elim (ha (Set.subset_univ _))⟩

def coordinateGeneralResidueSingle (m n : ℕ) (hc : Fintype.card σ = n+1)
    (e : ProjectiveNegativeWeight σ m) (r : coordinateCanonicalBaseRing R) :
    coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) n :=
  coordinateHomogeneousLaurentWeightInclusion (R := R) _ e.1 n
    (coordinateGeneralTopWeightCochain m n hc e r)

theorem coordinateGeneralResidue_single_same (m n : ℕ) (hc : Fintype.card σ = n+1)
    (e : ProjectiveNegativeWeight σ m) (r : coordinateCanonicalBaseRing R) :
    coordinateGeneralResidue (R := R) m n hc (coordinateGeneralResidueSingle m n hc e r) e = r := by
  change (coordinateHomogeneousLaurentWeightComponent (R := R) _ e.1 n
    (coordinateHomogeneousLaurentWeightInclusion (R := R) _ e.1 n _)).1 _ = r
  rw [coordinateHomogeneousLaurentWeightComponent_inclusion]
  rfl

theorem coordinateGeneralResidue_single_ne (m n : ℕ) (hc : Fintype.card σ = n+1)
    (e f : ProjectiveNegativeWeight σ m) (h : f ≠ e) (r : coordinateCanonicalBaseRing R) :
    coordinateGeneralResidue (R := R) m n hc (coordinateGeneralResidueSingle m n hc e r) f = 0 := by
  change (coordinateHomogeneousLaurentWeightComponent (R := R) _ f.1 n
    (coordinateHomogeneousLaurentWeightInclusion (R := R) _ e.1 n _)).1 _ = 0
  rw [coordinateHomogeneousLaurentWeightComponent_inclusion_ne _ e.1 f.1
    (fun he => h (Subtype.ext he))]
  rfl

/-- Every finite collection of negative-weight coefficients is represented
by an actual top cochain. Finiteness follows from the proved monomial
complement equivalence and mathlib's finite bounded-degree theorem. -/
theorem coordinateGeneralResidue_surjective (m n : ℕ) (hc : Fintype.card σ = n+1) :
    Function.Surjective (coordinateGeneralResidue (R := R) m n hc) := by
  classical
  letI := Fintype.ofFinite (ProjectiveNegativeWeight σ m)
  intro v
  refine ⟨∑ e, coordinateGeneralResidueSingle m n hc e (v e),?_⟩
  ext f
  rw [map_sum,Finset.sum_apply]
  rw [Finset.sum_eq_single f]
  · exact coordinateGeneralResidue_single_same m n hc f (v f)
  · intro e _ hef
    exact coordinateGeneralResidue_single_ne m n hc e f (Ne.symm hef) (v e)
  · simp

/-- The actual top quotient has exactly the full-negative monomial coordinates. -/
def coordinateGeneralTopQuotientEquiv (m n : ℕ) (hc : Fintype.card σ = n+2) :
    (coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) (n+1) ⧸
      LinearMap.range (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) n).hom)
      ≃ₗ[coordinateCanonicalBaseRing R]
        (ProjectiveNegativeWeight σ m → coordinateCanonicalBaseRing R) :=
  (Submodule.quotEquivOfEq _ _ (coordinateGeneralResidue_ker_eq_range m n hc).symm).trans
    ((coordinateGeneralResidue (R := R) m (n+1) hc).quotKerEquivOfSurjective
      (coordinateGeneralResidue_surjective m (n+1) hc))
end MvPolynomial
