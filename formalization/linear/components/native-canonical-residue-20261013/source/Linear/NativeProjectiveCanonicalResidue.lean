module
public import Linear.ProjectiveCanonicalCokernel
public import Linear.NativeProjectiveLaurentComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} {σ : Type} [Field K] [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual native integer-twist Cech term, retaining the original
Proj scheme, coordinate opens and module sheaf. -/
abbrev coordinateNativeCanonicalCechTerm (n : ℕ) :=
  Scheme.Modules.orderedBaseCechObject (homogeneousProjπ (R := K) (σ := σ))
    (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(Fintype.card σ : ℤ)))
    (coordinateOpenCover (R := K) (σ := σ)) n

/-- The actual geometric Cech differential on the native canonical twist. -/
abbrev coordinateNativeCanonicalCechDifferential (n : ℕ) :=
  Scheme.Modules.orderedBaseCechDifferential (homogeneousProjπ (R := K) (σ := σ))
    (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(Fintype.card σ : ℤ)))
    (coordinateOpenCover (R := K) (σ := σ)) n

/-- Actual native Cech residue, transported through the already verified
all-integer Laurent comparison, including every coface. -/
def coordinateNativeCanonicalResidue (n : ℕ) (hc : Fintype.card σ = n+1) :
    coordinateNativeCanonicalCechTerm (K := K) (σ := σ) n →ₗ[coordinateCanonicalBaseRing K]
      coordinateCanonicalBaseRing K :=
  (coordinateCanonicalResidue (R := K) n hc).comp
    (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) n).hom.hom

theorem coordinateNativeCanonicalLaurentDifferential_apply (n : ℕ)
    (t : coordinateNativeCanonicalCechTerm (K := K) (σ := σ) n) :
    (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) n).hom
      ((coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
        (-(Fintype.card σ : ℤ)) n).hom.hom t) =
    (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) (n+1)).hom.hom
      ((coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) n).hom t) := by
  exact congrArg (fun f => f.hom t)
    (coordinateNativeLaurentOrderedCechDifferential_naturality
      (K := K) (σ := σ) (-(Fintype.card σ : ℤ)) n)

theorem coordinateNativeCanonicalResidue_surjective (n : ℕ)
    (hc : Fintype.card σ = n+1) :
    Function.Surjective (coordinateNativeCanonicalResidue (K := K) n hc) := by
  intro r
  let s := coordinateCanonicalResidueSection (R := K) n hc r
  let e := coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
    (-(Fintype.card σ : ℤ)) n
  refine ⟨e.inv.hom s,?_⟩
  have he : e.hom.hom (e.inv.hom s) = s := by
    simpa using congrArg (fun f => f.hom s) e.inv_hom_id
  change coordinateCanonicalResidue (R := K) n hc (e.hom.hom (e.inv.hom s)) = r
  rw [he]
  exact coordinateCanonicalResidue_section n hc r

theorem coordinateNativeCanonicalResidue_boundary (n : ℕ)
    (hc : Fintype.card σ = n+2)
    (t : coordinateNativeCanonicalCechTerm (K := K) (σ := σ) n) :
    coordinateNativeCanonicalResidue (K := K) (n+1) hc
      ((coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) n).hom t) = 0 := by
  change coordinateCanonicalResidue (R := K) (n+1) hc
    ((coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) (n+1)).hom.hom
      ((coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) n).hom t)) = 0
  rw [← coordinateNativeCanonicalLaurentDifferential_apply]
  exact coordinateCanonicalResidue_boundary n hc _

/-- The ACTUAL geometric residue kernel is the ACTUAL native boundary
image. The target and comparison maps are constructed, not hypotheses. -/
theorem coordinateNativeCanonicalResidue_ker_eq_range (n : ℕ)
    (hc : Fintype.card σ = n+2) :
    LinearMap.ker (coordinateNativeCanonicalResidue (K := K) (n+1) hc) =
      LinearMap.range (coordinateNativeCanonicalCechDifferential (K := K) (σ := σ) n).hom := by
  ext s
  constructor
  · intro hs
    let e := coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) n
    let e' := coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) (n+1)
    obtain ⟨t,ht⟩ := exists_preimage_coordinateCanonicalResidue_zero n hc
      (e'.hom.hom s) hs
    refine ⟨e.inv.hom t,?_⟩
    have hi : Function.Injective e'.hom.hom :=
      (ModuleCat.mono_iff_injective e'.hom).mp inferInstance
    apply hi
    rw [← coordinateNativeCanonicalLaurentDifferential_apply]
    have he : e.hom.hom (e.inv.hom t) = t := by
      simpa using congrArg (fun f => f.hom t) e.inv_hom_id
    change (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ)
      (-(Fintype.card σ : ℤ)) n).hom (e.hom.hom (e.inv.hom t)) = e'.hom.hom s
    rw [he,ht]
  · rintro ⟨t,rfl⟩
    exact coordinateNativeCanonicalResidue_boundary n hc t
end MvPolynomial
