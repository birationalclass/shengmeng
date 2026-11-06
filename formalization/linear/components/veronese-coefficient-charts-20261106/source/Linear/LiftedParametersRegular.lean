module
public import Linear.ParameterSubstitution
public import Linear.NilpotentRegular
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Linear.Target

@[expose] public section
/-! Actual arbitrary parameter lifts are regular in a local Noetherian finite-flat thickening with reduction identified with the parameter ring. No new parameter action or perfect pairing is assumed. -/
open RingTheory.Sequence
namespace LinearStudy
theorem arbitrary_parameter_lifts_regular
    {K A : Type*} [Field K] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (hr : 0 < r)
    [Algebra (MvPowerSeries (Fin r) K) A] [Module.Flat (MvPowerSeries (Fin r) K) A]
    (q : A →ₐ[MvPowerSeries (Fin r) K] MvPowerSeries (Fin r) K)
    (hq : RingHom.ker q.toRingHom = nilradical A)
    (tau : Fin r → A)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    IsRegular A (List.ofFn tau) := by
  let B := MvPowerSeries (Fin r) K
  let T : Fin r → B := fun i => q (tau i)
  let old : Fin r → A := fun i => algebraMap B A (T i)
  have hsur : Function.Surjective q := fun b => ⟨algebraMap B A b, q.commutes b⟩
  let : IsLocalHom q.toRingHom := IsLocalHom.of_surjective q.toRingHom hsur
  have hmem (i : Fin r) : T i ∈ IsLocalRing.maximalIdeal B := by
    rw [← htau]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hmap (i : Fin r) : q (old i) = T i := q.commutes _
  have hold : ∀ x ∈ List.ofFn old, x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    rw [← IsLocalRing.maximalIdeal_comap q.toRingHom]
    change q (old i) ∈ IsLocalRing.maximalIdeal B
    rw [hmap]
    exact hmem i
  have htmem : ∀ x ∈ List.ofFn tau, x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    rw [← IsLocalRing.maximalIdeal_comap q.toRingHom]
    exact hmem i
  have hw := (powerSeries_parameter_generators_regular hr T htau).toIsWeaklyRegular.of_flat
    (S := A)
  rw [List.map_ofFn] at hw
  have hreg : IsRegular A (List.ofFn old) :=
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A hold hw
  apply regular_nilpotent_perturbation (List.ofFn old) (List.ofFn tau) hreg hold htmem
  rw [show List.ofFn old = (List.ofFn (fun i : Fin r => i)).map old by
    rw [List.map_ofFn]; rfl]
  rw [show List.ofFn tau = (List.ofFn (fun i : Fin r => i)).map tau by
    rw [List.map_ofFn]; rfl]
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro i _
  apply mem_nilradical.mp
  rw [← hq]
  change q (tau i - old i) = 0
  rw [map_sub, hmap]
  exact sub_self _
theorem completeIntersection_parameter_lifts_regular
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hr : 0 < r)
    (hH : IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    IsRegular (CompleteIntersection H) (List.ofFn tau) := by
  have hI : equationIdeal H ≠ ⊤ := by
    intro ht
    apply hH.top_ne_smul
    rw [show Ideal.ofList (List.ofFn H) = equationIdeal H by
      simp [Ideal.ofList, equationIdeal, List.mem_ofFn, Set.range], ht,
      Submodule.top_smul]
  let : Nontrivial (CompleteIntersection H) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (CompleteIntersection H) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (equationIdeal H)) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (CompleteIntersection H) := isNoetherianRing_of_surjective
    (AmbientRing r c) _ (Ideal.Quotient.mk (equationIdeal H)) Ideal.Quotient.mk_surjective
  exact arbitrary_parameter_lifts_regular hr q hq tau htau
end LinearStudy
