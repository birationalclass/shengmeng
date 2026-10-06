module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section
open scoped Pointwise PowerSeries
open RingTheory.Sequence

namespace LinearStudy

variable {R : Type*} [CommRing R]

theorem regular_transport_ringEquiv {S : Type*} [CommRing S]
    (e : R ≃+* S) (rs : List R) :
    IsRegular R rs ↔ IsRegular S (rs.map e) := by
  apply e.toAddEquiv.isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r hr x
  exact e.map_mul r x

theorem powerSeries_cons_X_regular (rs : List R) (hr : IsRegular R rs) :
    IsRegular R⟦X⟧ (PowerSeries.X :: rs.map PowerSeries.C) := by
  rw [isRegular_cons_iff]
  refine ⟨PowerSeries.X_mul_injective, ?_⟩
  have hs : (PowerSeries.X : R⟦X⟧) • (⊤ : Submodule R⟦X⟧ R⟦X⟧) =
      (Ideal.span {PowerSeries.X} : Ideal R⟦X⟧) := by
    rw [← Submodule.ideal_span_singleton_smul]
    exact Ideal.mul_top _
  have hk : (Ideal.span {PowerSeries.X} : Ideal R⟦X⟧) =
      RingHom.ker (PowerSeries.constantCoeff (R := R)) := by
    ext f
    simp [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
  let e := ((Submodule.quotEquivOfEq _ _ hs).toAddEquiv.trans
    (Ideal.quotEquivOfEq hk).toAddEquiv).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := PowerSeries.constantCoeff (R := R))
      (fun r => ⟨PowerSeries.C r, by simp⟩)).toAddEquiv
  apply (e.isRegular_congr (as := rs.map PowerSeries.C) (bs := rs) ?_).mpr hr
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_same.mpr
  intro r hr x
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  change PowerSeries.constantCoeff (PowerSeries.C r * f) = r * PowerSeries.constantCoeff f
  simp

theorem powerSeries_variables_regular [Nontrivial R] (n : ℕ) :
    IsRegular (MvPowerSeries (Fin n) R)
      (List.ofFn (MvPowerSeries.X (σ := Fin n) (R := R))) := by
  induction n with
  | zero => simpa using IsRegular.nil (MvPowerSeries (Fin 0) R) _
  | succ n ih =>
    apply (regular_transport_ringEquiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv _).mpr
    simpa [List.ofFn_succ, List.map_ofFn, Function.comp_def,
      MvPowerSeries.finSuccEquiv_X_succ] using powerSeries_cons_X_regular _ ih

end LinearStudy
