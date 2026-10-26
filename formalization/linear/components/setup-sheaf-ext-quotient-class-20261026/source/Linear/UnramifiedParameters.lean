module
public import Linear.ParameterLinearPart
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.AdicCompletion.LocalRing
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

theorem unramified_local_parameters_generate {R S ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (t : ι → R) (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal R) :
    Ideal.span (Set.range (fun i => algebraMap R S (t i))) = IsLocalRing.maximalIdeal S := by
  have h := congrArg (fun I : Ideal R => I.map (algebraMap R S)) ht
  rw [Ideal.map_span, ← Set.range_comp, Algebra.FormallyUnramified.map_maximalIdeal] at h
  exact h

theorem unramified_completed_parameters_generate {R S ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S]
    (t : ι → R) (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal R) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal S) S
    Ideal.span (Set.range (fun i => algebraMap S C (algebraMap R S (t i)))) =
      IsLocalRing.maximalIdeal C := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal S) S
  have h := congrArg (fun I : Ideal S => I.map (algebraMap S C))
    (unramified_local_parameters_generate t ht)
  rw [Ideal.map_span, ← Set.range_comp, ← AdicCompletion.maximalIdeal_eq_map] at h
  exact h

theorem unramified_completed_parameters_coordinates {R S K : Type*} {r : ℕ}
    [CommRing R] [CommRing S] [Field K] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S]
    (t : Fin r → R) (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal R)
    (e : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* MvPowerSeries (Fin r) K) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal S) S
    let T := fun i => e (algebraMap S C (algebraMap R S (t i)))
    Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
      IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal S) S
  let T := fun i => e (algebraMap S C (algebraMap R S (t i)))
  have h := congrArg (fun I : Ideal C => I.map e.toRingHom)
    (unramified_completed_parameters_generate t ht)
  rw [Ideal.map_span, ← Set.range_comp] at h
  have hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) :=
    h.trans (IsLocalRing.map_ringEquiv_maximalIdeal e)
  exact ⟨hT, parameter_generators_jacobian_constantCoeff_unit T hT⟩

end LinearStudy
