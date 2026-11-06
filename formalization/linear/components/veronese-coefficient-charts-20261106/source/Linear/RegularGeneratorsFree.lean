module
public import Linear.NilpotentRegular
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section
/-! Freeness of a finite module whose weakly regular sequence generates the maximal ideal of a local Noetherian ring. Uses mathlib's lifting of freeness modulo one regular element. -/
open RingTheory.Sequence
universe u v
namespace LinearStudy
theorem free_of_regular_maximal_generators
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (h : IsWeaklyRegular M rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R) : Module.Free R M := by
  let motive := fun (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] (rs : List R) =>
      ∀ [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M],
        Ideal.ofList rs = IsLocalRing.maximalIdeal R → Module.Free R M
  apply h.ndrecWithRing (motive := motive) ?_ ?_ hgen
  · intro R _ M _ _ _ _ _ hgen
    have hf : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr (by
      simpa using hgen.symm)
    let : Field R := hf.toField
    infer_instance
  · intro R _ M _ _ x xs hx hxs ih _ _ _ hgen
    have hxm : x ∈ IsLocalRing.maximalIdeal R := by
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    have hI : Ideal.span {x} ≠ (⊤ : Ideal R) :=
      ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (by simpa using hxm)
    let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hI
    let : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    let : IsNoetherianRing (R ⧸ Ideal.span {x}) :=
      isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    have hquot : Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) =
        IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective, ← hgen,
        Ideal.ofList_cons, Ideal.map_sup, Ideal.map_span]
      simp [Ideal.map_ofList]
    let : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
    have hf := ih hquot
    let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    exact (Module.free_quotSMulTop_iff_free R M
      (IsLocalRing.maximalIdeal_le_jacobson ⊥ hxm) hx).mp hf
theorem free_of_regular_maximal_algebraMap
    {R A : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A]
    (rs : List R)
    (h : IsWeaklyRegular A (rs.map (algebraMap R A)))
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R) : Module.Free R A := by
  exact free_of_regular_maximal_generators rs
    ((isWeaklyRegular_map_algebraMap_iff (R := R) (S := A) (M := A) rs).mp h) hgen
end LinearStudy
