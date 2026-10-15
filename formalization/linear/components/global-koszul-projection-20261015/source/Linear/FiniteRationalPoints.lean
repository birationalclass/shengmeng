module
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- A finite-dimensional commutative algebra has only finitely many actual
rational points. Kernel equality determines the K-valued algebra homomorphism. -/
theorem finite_rational_points_of_module_finite
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] : Finite (A →ₐ[K] K) := by
  let : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let j : (A →ₐ[K] K) → PrimeSpectrum A := fun φ =>
    ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime φ.toRingHom⟩
  apply Finite.of_injective j
  intro φ ψ h
  have hk : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom :=
    congrArg PrimeSpectrum.asIdeal h
  apply AlgHom.ext
  intro a
  have hz : a - algebraMap K A (φ a) ∈ RingHom.ker φ.toRingHom := by
    change φ (a - algebraMap K A (φ a)) = 0
    simp
  rw [hk] at hz
  change ψ (a - algebraMap K A (φ a)) = 0 at hz
  have he : ψ a = φ a := by
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_eq_zero] using hz
  exact he.symm

/-- This is the actual affine zero locus, injected into rational points of
its quotient algebra. No finiteness of the zero set is assumed. -/
theorem polynomial_zeroLocus_finite_of_module_finite
    {K ι : Type*} [Field K] (I : Ideal (MvPolynomial ι K))
    [Module.Finite K (MvPolynomial ι K ⧸ I)] :
    (MvPolynomial.zeroLocus K I).Finite := by
  let Q := MvPolynomial ι K ⧸ I
  let j : MvPolynomial.zeroLocus K I → (Q →ₐ[K] K) := fun x =>
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval (R := K) x.1) x.2
  let : Finite (Q →ₐ[K] K) := finite_rational_points_of_module_finite
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    funext i
    have hi := AlgHom.congr_fun h (Ideal.Quotient.mk I (MvPolynomial.X i))
    change MvPolynomial.aeval (R := K) x.1 (MvPolynomial.X i) =
      MvPolynomial.aeval (R := K) y.1 (MvPolynomial.X i) at hi
    simpa only [MvPolynomial.aeval_X] using hi
  let : Finite (MvPolynomial.zeroLocus K I) := Finite.of_injective j hj
  exact Set.toFinite _

end LinearStudy
