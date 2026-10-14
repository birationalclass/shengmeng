module
public import Linear.GenericSmoothOpen
public import Linear.FiniteTypeRationalPoint
public import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

def rationalPointPrime {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (ρ : A →ₐ[K] K) : PrimeSpectrum A :=
  ⟨RingHom.ker ρ.toRingHom, RingHom.ker_isPrime _⟩

/-- A finite-type integral algebra over an algebraically closed perfect
field has an actual rational point in a constructed smooth principal open. -/
theorem domain_exists_smooth_rational_point
    {K A : Type*} [Field K] [IsAlgClosed K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FinitePresentation K A] :
    ∃ (a : A) (ρ : A →ₐ[K] K), a ≠ 0 ∧ ρ a ≠ 0 ∧
      rationalPointPrime ρ ∈ Algebra.smoothLocus K A := by
  obtain ⟨a, ha, hs⟩ := domain_exists_nonzero_smooth_basic_open (K := K) (A := A)
  let B := Localization.Away a
  have hi : Function.Injective (algebraMap A B) := IsLocalization.injective B
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  letI : Nontrivial B := Function.Injective.nontrivial hi
  letI : Algebra.Smooth K B := hs
  obtain ⟨φ⟩ := finiteType_exists_rational_point (K := K) (A := B)
  let ρ := φ.comp (IsScalarTower.toAlgHom K A B)
  let p := rationalPointPrime φ
  have hu : ρ a ≠ 0 := isUnit_iff_ne_zero.mp
    ((IsLocalization.Away.algebraMap_isUnit a (S := B)).map φ)
  have hp : p ∈ Algebra.smoothLocus K B := by
    rw [Algebra.smoothLocus_eq_univ]
    trivial
  have hpA : PrimeSpectrum.comap (algebraMap A B) p ∈ Algebra.smoothLocus K A := by
    have h := congrArg (fun S : Set (PrimeSpectrum B) => p ∈ S)
      (Algebra.smoothLocus_comap_of_isLocalization (R := K) (Af := B) a)
    exact h.mpr hp
  have he : PrimeSpectrum.comap (algebraMap A B) p = rationalPointPrime ρ := by
    apply PrimeSpectrum.ext
    change (RingHom.ker φ.toRingHom).comap (algebraMap A B) =
      RingHom.ker ρ.toRingHom
    rw [RingHom.comap_ker]
    rfl
  exact ⟨a, ρ, ha, hu, he ▸ hpA⟩

end LinearStudy
