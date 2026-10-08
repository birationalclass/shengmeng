module
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- An actual integral injective algebra preserves Krull dimension:
chains lift by going up, and contraction preserves strict inclusions. -/
theorem integral_injective_ringKrullDim_eq
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  apply le_antisymm
  · unfold ringKrullDim Order.krullDim
    apply sSup_le
    rintro _ ⟨l, rfl⟩
    let P := Classical.choice (inferInstance : Nonempty (Ideal.primesOver l.head.asIdeal S))
    letI : P.val.IsPrime := P.property.1
    letI : P.val.LiesOver l.head.asIdeal := P.property.2
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.val
    change (l.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum S)
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro P Q hPQ
    letI : P.asIdeal.IsPrime := P.isPrime
    exact Ideal.IsIntegral.under_lt_under (show P.asIdeal < Q.asIdeal from hPQ)

end LinearStudy
