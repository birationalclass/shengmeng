module

public import Negativity.LocalPushPull
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDiscreteValuationRing

noncomputable def DvrRationalOrder (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) : ℤ :=
  LocalFractionOrder R (IsLocalization.sec (nonZeroDivisors R) (a : K)).1
    (IsLocalization.sec (nonZeroDivisors R) (a : K)).2

/-- The signed order of an actual fraction-field element is computed by any
nonzero numerator and denominator representing it. -/
theorem dvr_rationalOrder_represents (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (r s : R) (hr : r ≠ 0) (hs : s ≠ 0)
    (heq : (a : K) * algebraMap R K s = algebraMap R K r) :
    DvrRationalOrder R K a = LocalFractionOrder R r s := by
  let b := IsLocalization.sec (nonZeroDivisors R) (a : K)
  have hb : (b.2 : R) ≠ 0 := nonZeroDivisors.ne_zero b.2.2
  have he : (a : K) * algebraMap R K (b.2 : R) = algebraMap R K b.1 :=
    IsLocalization.sec_spec (nonZeroDivisors R) (a : K)
  have hn : b.1 ≠ 0 := by
    intro hz
    have hbk : algebraMap R K (b.2 : R) ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R K).ne hb
    have hm := mul_ne_zero a.ne_zero hbk
    apply hm
    exact he.trans (by rw [hz, map_zero])
  apply dvr_fraction_order_well_defined b.1 b.2 r s hn hb hr hs
  apply IsFractionRing.injective R K
  simp only [map_mul]
  rw [← he, ← heq]
  ring

/-- Regular units have zero rational order in the actual fraction field. -/
theorem dvr_rationalOrder_unit (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (u : Rˣ) :
    DvrRationalOrder R K (Units.map (algebraMap R K : R →* K) u) = 0 := by
  rw [dvr_rationalOrder_represents R K _ (u : R) 1 u.ne_zero one_ne_zero (by simp)]
  simp [LocalFractionOrder, addVal_eq_zero_of_unit]

/-- Multiplication of nonzero rational local equations adds their orders. -/
theorem dvr_rationalOrder_mul (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (a c : Kˣ) :
    DvrRationalOrder R K (a * c) = DvrRationalOrder R K a + DvrRationalOrder R K c := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) (a : K)
  obtain ⟨⟨t, v⟩, h'⟩ := IsLocalization.surj (nonZeroDivisors R) (c : K)
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hv : (v : R) ≠ 0 := nonZeroDivisors.ne_zero v.2
  have hsk : algebraMap R K (s : R) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hs
  have hvk : algebraMap R K (v : R) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hv
  have hr : r ≠ 0 := by
    intro hz
    exact mul_ne_zero a.ne_zero hsk (by simpa only [hz, map_zero] using h)
  have ht : t ≠ 0 := by
    intro hz
    exact mul_ne_zero c.ne_zero hvk (by simpa only [hz, map_zero] using h')
  rw [dvr_rationalOrder_represents R K (a * c) (r*t) (s*v)
    (mul_ne_zero hr ht) (mul_ne_zero hs hv) (by
      simp only [Units.val_mul, map_mul]
      calc
        (a : K) * (c : K) * (algebraMap R K s * algebraMap R K v) =
            ((a : K) * algebraMap R K s) * ((c : K) * algebraMap R K v) := by ring
        _ = algebraMap R K r * algebraMap R K t := by rw [h, h']),
    dvr_rationalOrder_represents R K a r s hr hs h,
    dvr_rationalOrder_represents R K c t v ht hv h']
  have vr : addVal R r ≠ ⊤ := fun h ↦ hr (addVal_eq_top_iff.mp h)
  have vt : addVal R t ≠ ⊤ := fun h ↦ ht (addVal_eq_top_iff.mp h)
  have vs : addVal R (s : R) ≠ ⊤ := fun h ↦ hs (addVal_eq_top_iff.mp h)
  have vv : addVal R (v : R) ≠ ⊤ := fun h ↦ hv (addVal_eq_top_iff.mp h)
  simp only [LocalFractionOrder, addVal_mul, ENat.toNat_add vr vt,
    ENat.toNat_add vs vv, Nat.cast_add]
  ring

/-- The unit transition in a Cartier presentation does not change the
coefficient. The unit belongs to the actual local ring. -/
theorem dvr_rationalOrder_unit_transition (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (u : Rˣ) (a : Kˣ) :
    DvrRationalOrder R K (Units.map (algebraMap R K : R →* K) u * a) =
      DvrRationalOrder R K a := by
  rw [dvr_rationalOrder_mul, dvr_rationalOrder_unit, zero_add]

end Negativity
