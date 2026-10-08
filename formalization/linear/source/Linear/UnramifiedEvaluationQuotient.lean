module
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.Field
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K R A Q : Type*} [Field K] [CommRing R] [CommRing A] [CommRing Q]
  [Algebra K Q] [Algebra.EssFiniteType K Q]

/-- An actual surjective fiber quotient whose composite is target evaluation
inherits reducedness from an unramified open containing that whole quotient. -/
theorem isReduced_of_unramified_evaluation_quotient
    (φ : R →+* A) (ρ : R →+* K) (ψ : A →+* Q) (b : R)
    (hψ : Function.Surjective ψ)
    (hcomp : ψ.comp φ = (algebraMap K Q).comp ρ)
    (hb : ρ b ≠ 0)
    (hgood : letI : Algebra R A := φ.toAlgebra
      ↑(PrimeSpectrum.basicOpen (φ b)) ⊆ Algebra.unramifiedLocus R A) :
    IsReduced Q := by
  letI : Algebra R A := φ.toAlgebra
  let A' := Localization.Away (φ b)
  have hunram : Algebra.FormallyUnramified R A' :=
    Algebra.basicOpen_subset_unramifiedLocus_iff.mp hgood
  letI := hunram
  have hunit : IsUnit (ψ (φ b)) := by
    have he := RingHom.congr_fun hcomp b
    change ψ (φ b) = algebraMap K Q (ρ b) at he
    rw [he]
    exact (isUnit_iff_ne_zero.mpr hb).map (algebraMap K Q)
  let τ : A' →+* Q := IsLocalization.Away.lift (φ b) hunit
  have hτ : Function.Surjective τ := by
    intro q
    obtain ⟨a, ha⟩ := hψ q
    refine ⟨algebraMap A A' a, ?_⟩
    simpa [τ] using ha
  have hφ' : ((algebraMap A A').comp φ).FormallyUnramified := by
    have ha : (algebraMap R A').FormallyUnramified :=
      RingHom.formallyUnramified_algebraMap.mpr hunram
    exact ha
  have hc : (τ.comp ((algebraMap A A').comp φ)).FormallyUnramified :=
    hφ'.comp (RingHom.FormallyUnramified.of_surjective hτ)
  have he : τ.comp ((algebraMap A A').comp φ) = ψ.comp φ := by
    ext r
    simp [τ]
  rw [he, hcomp] at hc
  have hK : Algebra.FormallyUnramified K Q :=
    RingHom.formallyUnramified_algebraMap.mp (RingHom.FormallyUnramified.of_comp hc)
  letI := hK
  exact Algebra.FormallyUnramified.isReduced_of_field K Q

end LinearStudy
