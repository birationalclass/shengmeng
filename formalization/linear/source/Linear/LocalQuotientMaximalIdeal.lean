module
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
theorem point_local_quotient_maximalIdeal_map {R : Type*} [CommRing R]
    (I P : Ideal R) [P.IsPrime]
    [IsLocalRing (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))] :
    (P.map (algebraMap R (Localization.AtPrime P))).map
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime P)))) =
        IsLocalRing.maximalIdeal
          (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
end LinearStudy
