module

public import Linear.Target
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Arbitrary parameter lifts: the Artinian quotient and its maximal ideal

This proves the first two conclusions of the parameter-lift part of the
relative Jacobian target for an arbitrary Noetherian nilpotent thickening.
It does not assert that the Jacobian survives the quotient or generates
its socle. Those are separate complete-intersection obligations.
-/

@[expose] public section
namespace LinearStudy

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
  [IsLocalRing B]

/-- The lifted parameter ideal plus the reduction kernel is the preimage
of the maximal ideal of the base. -/
theorem liftedIdeal_sup_kernel (q : A →ₐ[B] B) (J : Ideal A)
    (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal B) :
    J ⊔ RingHom.ker q.toRingHom =
      (IsLocalRing.maximalIdeal B).comap q.toRingHom := by
  have hs : Function.Surjective q := fun b => ⟨algebraMap B A b, q.commutes b⟩
  rw [← hJ, Ideal.comap_map_of_surjective q.toRingHom hs]
  rfl

/-- Arbitrary lifts generating the base maximal ideal give a quotient
whose image of the original nilradical is already maximal. -/
theorem parameterQuotient_nilradical_image_isMaximal
    (q : A →ₐ[B] B) (hq : RingHom.ker q.toRingHom = nilradical A)
    (J : Ideal A) (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal B) :
    ((nilradical A).map (Ideal.Quotient.mk J)).IsMaximal := by
  have hs : Function.Surjective q := fun b => ⟨algebraMap B A b, q.commutes b⟩
  have hM : (J ⊔ nilradical A).IsMaximal := by
    rw [← hq, liftedIdeal_sup_kernel q J hJ]
    exact Ideal.comap_isMaximal_of_surjective _ hs
  let := hM
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (m := J ⊔ nilradical A) (by simp)
  simpa [Ideal.map_sup] using hm

/-- In that quotient there are no extra nilpotents beyond the image of
the original nilradical. -/
theorem parameterQuotient_nilradical_eq
    (q : A →ₐ[B] B) (hq : RingHom.ker q.toRingHom = nilradical A)
    (J : Ideal A) (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal B) :
    nilradical (A ⧸ J) = (nilradical A).map (Ideal.Quotient.mk J) := by
  let := parameterQuotient_nilradical_image_isMaximal q hq J hJ
  apply le_antisymm (nilradical_le_prime _)
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  exact mem_nilradical.mpr ((mem_nilradical.mp ha).map (Ideal.Quotient.mk J))

/-- The quotient by arbitrary lifted parameters is local Artinian when
the original algebra is Noetherian. No pairing or socle assumption is used. -/
theorem parameterQuotient_local_artinian [IsNoetherianRing A]
    (q : A →ₐ[B] B) (hq : RingHom.ker q.toRingHom = nilradical A)
    (J : Ideal A) (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal B) :
    IsArtinianRing (A ⧸ J) ∧ IsLocalRing (A ⧸ J) := by
  have hm : (nilradical (A ⧸ J)).IsMaximal := by
    rw [parameterQuotient_nilradical_eq q hq J hJ]
    exact parameterQuotient_nilradical_image_isMaximal q hq J hJ
  have hd := ((Ring.krullDimLE_zero_and_isLocalRing_tfae (A ⧸ J)).out
    4 1 rfl rfl).mp hm
  let := hd.1
  let := isNoetherianRing_of_surjective A (A ⧸ J)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  exact ⟨IsNoetherianRing.isArtinianRing_of_krullDimLE_zero, hd.2⟩

/-- Apply the general ideal result to an actual finite list of parameter
lifts; the only hypothesis is their stated generation in the base. -/
theorem arbitraryParameterLifts_artinian [IsNoetherianRing A]
    {ι : Type*} (q : A →ₐ[B] B)
    (hq : RingHom.ker q.toRingHom = nilradical A) (tau : ι → A)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal B) :
    let J := Ideal.span (Set.range tau)
    IsArtinianRing (A ⧸ J) ∧
      ((nilradical A).map (Ideal.Quotient.mk J)).IsMaximal := by
  have hJ : (Ideal.span (Set.range tau)).map q.toRingHom =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_span]
    rw [← Set.range_comp]
    exact htau
  exact ⟨(parameterQuotient_local_artinian q hq _ hJ).1,
    parameterQuotient_nilradical_image_isMaximal q hq _ hJ⟩

/-- The Artinian and maximal-ideal portion of the manuscript's exact
multivariable power-series target, for every permitted parameter lift.
The regular-sequence and flatness hypotheses are not needed for this part. -/
theorem completeIntersection_parameterQuotient_artinian {r c : ℕ}
    (H : Fin c → AmbientRing r c)
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    let J := Ideal.span (Set.range tau)
    IsArtinianRing (CompleteIntersection H ⧸ J) ∧
      ((nilradical (CompleteIntersection H)).map (Ideal.Quotient.mk J)).IsMaximal := by
  let := isNoetherianRing_of_surjective (AmbientRing r c) (CompleteIntersection H)
    (Ideal.Quotient.mk (equationIdeal H)) Ideal.Quotient.mk_surjective
  exact arbitraryParameterLifts_artinian q hq tau htau

end LinearStudy
