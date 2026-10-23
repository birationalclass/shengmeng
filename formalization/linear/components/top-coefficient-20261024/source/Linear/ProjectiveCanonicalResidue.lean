module
public import Linear.ProjectiveLaurentTopWeight
public import Linear.OrderedCechFullSupport
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]
abbrev coordinateCanonicalBaseRing (R : Type u) [CommRing R] :=
  Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))

/-- The coefficient of (-1,...,-1) at the actual increasing full Cech tuple.
This uses the actual homogeneous Laurent presentation of all chart sections. -/
def coordinateCanonicalResidue (n : ℕ) (hc : Fintype.card σ = n+1) :
    coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n →ₗ[coordinateCanonicalBaseRing R]
      coordinateCanonicalBaseRing R where
  toFun s := (coordinateHomogeneousLaurentWeightComponent (R := R)
    (-(Fintype.card σ : ℤ)) (HomogeneousLaurentExponent.canonicalNegative σ) n s).1
    (LinearStudy.orderedCechFullIndex n (by simpa using hc))
  map_add' s t := by simp
  map_smul' r s := by simp

/-- A constant full-support cochain in the canonical weight. All top tuples
are proved equal to the full tuple; no range/splitting certificate is assumed. -/
def coordinateCanonicalTopCochain (n : ℕ) (hc : Fintype.card σ = n+1) :
    coordinateCanonicalBaseRing R →ₗ[coordinateCanonicalBaseRing R]
      LinearStudy.OrderedCechSupportCochain (coordinateCanonicalBaseRing R)
        (HomogeneousLaurentExponent.canonicalNegative σ).liftedNegativeSupport n where
  toFun r := ⟨fun _ => r,fun a ha => by
    have he := LinearStudy.orderedCechIndex_eq_full n (by simpa using hc) a
    rw [he,LinearStudy.orderedCechFullIndex_range] at ha
    exact False.elim (ha (Set.subset_univ _))⟩
  map_add' r s := rfl
  map_smul' r s := rfl

/-- Insert a multiple of the actual canonical Laurent monomial into the
actual top cochain. This is a section of the residue, not of the Cech differential. -/
def coordinateCanonicalResidueSection (n : ℕ) (hc : Fintype.card σ = n+1) :
    coordinateCanonicalBaseRing R →ₗ[coordinateCanonicalBaseRing R]
      coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n :=
  (coordinateHomogeneousLaurentWeightInclusion (R := R)
    (-(Fintype.card σ : ℤ)) (HomogeneousLaurentExponent.canonicalNegative σ) n).comp
    (coordinateCanonicalTopCochain (R := R) n hc)

theorem coordinateCanonicalResidue_section (n : ℕ) (hc : Fintype.card σ = n+1)
    (r : coordinateCanonicalBaseRing R) :
    coordinateCanonicalResidue (R := R) n hc
      (coordinateCanonicalResidueSection (R := R) n hc r) = r := by
  change (coordinateHomogeneousLaurentWeightComponent (R := R) _ _ n
    (coordinateHomogeneousLaurentWeightInclusion (R := R) _ _ n
      (coordinateCanonicalTopCochain (R := R) n hc r))).1 _ = r
  rw [coordinateHomogeneousLaurentWeightComponent_inclusion]
  rfl

theorem coordinateCanonicalResidue_surjective (n : ℕ)
    (hc : Fintype.card σ = n+1) :
    Function.Surjective (coordinateCanonicalResidue (R := R) n hc) := by
  intro r
  exact ⟨coordinateCanonicalResidueSection (R := R) n hc r,
    coordinateCanonicalResidue_section n hc r⟩

/-- The residue vanishes on every actual Cech boundary in positive top degree.
The canonical component one degree lower is zero by its required full support. -/
theorem coordinateCanonicalResidue_boundary (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (t : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n) :
    coordinateCanonicalResidue (R := R) (n+1) hc
      ((coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) (-(Fintype.card σ : ℤ)) n).hom t) = 0 := by
  have hz := LinearStudy.orderedCechSupport_eq_zero_of_full_support
    (coordinateCanonicalBaseRing R)
    (HomogeneousLaurentExponent.canonicalNegative σ).liftedNegativeSupport
    HomogeneousLaurentExponent.canonicalNegative_lifted_support n
    (by simp [hc])
    (coordinateHomogeneousLaurentWeightComponent (R := R)
      (-(Fintype.card σ : ℤ)) (HomogeneousLaurentExponent.canonicalNegative σ) n t)
  change (coordinateHomogeneousLaurentWeightComponent (R := R) _ _ (n+1)
    ((coordinateHomogeneousLaurentOrderedCechDifferential (R := R) _ n).hom t)).1 _ = 0
  rw [coordinateHomogeneousLaurentWeightComponent_differential,hz,map_zero]
  rfl

end MvPolynomial
