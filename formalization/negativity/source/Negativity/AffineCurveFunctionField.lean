module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
set_option backward.isDefEq.respectTransparency false

/-- An injective integral subring of a domain of dimension at most one
also has dimension at most one, by lying over and maximal contraction. -/
theorem integral_subring_krullDimLE_one
    (A R : Type*) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    [Algebra A R] [Algebra.IsIntegral A R] [Ring.KrullDimLE 1 R]
    (hinj : Function.Injective (algebraMap A R)) : Ring.KrullDimLE 1 A := by
  apply Ring.KrullDimLE.mk₁'
  intro P hP hp
  have := hp
  obtain ⟨Q, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := R) P
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have := hQ
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hP
    rw [← hQP, h]
    change RingHom.ker (algebraMap A R) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have : Q.IsMaximal := hQ.isMaximal_of_ne_bot hQ0
  rw [← hQP]
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q

/-- A finite-type domain of dimension at most one which is not a field
has transcendence degree exactly one over its constant field. -/
theorem affine_curve_ring_trdeg_one
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [Ring.KrullDimLE 1 R] (hR : ¬ IsField R) :
    Algebra.trdeg k R = 1 := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k R
  let A := MvPolynomial (Fin n) k
  let : Algebra A R := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral A R := ⟨hint⟩
  have hinj : Function.Injective (algebraMap A R) := hg
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hinj
  have : IsScalarTower k A R := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : Ring.KrullDimLE 1 A := integral_subring_krullDimLE_one A R hinj
  have hnle : n ≤ 1 := by
    have hdim := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
    change ringKrullDim (MvPolynomial (Fin n) k) ≤ 1 at hdim
    simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hdim
    exact_mod_cast hdim
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    have hA : IsField A :=
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv.toMulEquiv.isField
        (Field.toIsField k)
    exact hR (isField_of_isIntegral_of_isField' hA)
  have hn : n = 1 := by omega
  have heq := trdeg_add_eq k A (A := R)
  rw [trdeg_eq_zero (R := A) (A := R), add_zero] at heq
  rw [← heq]
  change Algebra.trdeg k (MvPolynomial (Fin n) k) = 1
  rw [MvPolynomial.trdeg_of_isDomain, hn]
  simp

/-- Final theorem: the fraction field of a genuine finite-type affine
curve domain is essentially of finite type and has transcendence degree one.
No separating parameter, finite field extension, or transcendence-degree
conclusion is assumed. The ring is required to be a non-field curve chart. -/
theorem affine_curve_fractionField_finiteType_trdeg_one
    (k R L : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [Ring.KrullDimLE 1 R] (hR : ¬ IsField R)
    [Field L] [Algebra R L] [IsFractionRing R L] [Algebra k L]
    [IsScalarTower k R L] :
    Algebra.EssFiniteType k L ∧ Algebra.trdeg k L = 1 := by
  have : Algebra.EssFiniteType R L :=
    Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors R)
  have hft : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k R L
  have : Algebra.IsAlgebraic R L := IsLocalization.isAlgebraic L (nonZeroDivisors R)
  have : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).mpr (IsFractionRing.injective R L)
  have heq := trdeg_add_eq k R (A := L)
  rw [trdeg_eq_zero (R := R) (A := L), add_zero, affine_curve_ring_trdeg_one k R hR] at heq
  exact ⟨hft, heq.symm⟩

end Negativity




