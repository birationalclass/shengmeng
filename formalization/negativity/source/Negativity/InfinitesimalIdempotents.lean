module

public import Negativity.ClopenCharacteristicSection
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual closed subscheme defined by the (n+1)st power of an actual
ideal sheaf. These are genuine infinitesimal thickenings, not ring models. -/
def actualPowerThickening {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) : Scheme.{u} :=
  (I ^ (n + 1)).subscheme

/-- Every positive power has the same actual closed support. -/
def actualPowerThickeningHomeomorph {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    actualPowerThickening I n ≃ₜ I.subscheme :=
  Homeomorph.setCongr (congrArg SetLike.coe (IdealSheafData.support_pow_succ I n))

/-- The actual immersion from a smaller to a larger infinitesimal
thickening, constructed by inclusion of powers of actual ideal sheaves. -/
def actualPowerThickeningInclusion {X : Scheme.{u}} (I : X.IdealSheafData)
    {m n : ℕ} (h : m ≤ n) : actualPowerThickening I m ⟶ actualPowerThickening I n :=
  IdealSheafData.inclusion (by
    intro U
    simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
      (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.add_le_add_right h 1)))

theorem actual_power_thickening_inclusion_point {X : Scheme.{u}}
    (I : X.IdealSheafData) {m n : ℕ} (h : m ≤ n)
    (x : actualPowerThickening I m) :
    actualPowerThickeningHomeomorph I n (actualPowerThickeningInclusion I h x) =
      actualPowerThickeningHomeomorph I m x := by
  apply Subtype.ext
  exact congrArg (fun f => f x) (IdealSheafData.inclusion_subschemeι
    (show I ^ (n + 1) ≤ I ^ (m + 1) from by
      intro U
      simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
        (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.add_le_add_right h 1))))

/-- The actual inverse-limit ring of regular functions on all actual
power thickenings, written explicitly as compatible families. Formal
functions must still compare this ring with a completed section ring. -/
def actualInfinitesimalSections {X : Scheme.{u}} (I : X.IdealSheafData) :
    Subring (∀ n : ℕ, Γ(actualPowerThickening I n, ⊤)) where
  carrier := {a | ∀ m n (h : m ≤ n), (actualPowerThickeningInclusion I h).appTop (a n) = a m}
  zero_mem' := by intro m n h; exact map_zero _
  one_mem' := by intro m n h; exact map_one _
  add_mem' := by
    intro a b ha hb m n h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (ha m n h) (hb m n h))
  mul_mem' := by
    intro a b ha hb m n h
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (ha m n h) (hb m n h))
  neg_mem' := by
    intro a ha m n h
    exact (map_neg _ _).trans (congrArg Neg.neg (ha m n h))

/-- Final theorem: a genuine disconnected closed subscheme constructs
a nontrivial idempotent in the actual inverse-limit ring of functions on
its genuine infinitesimal thickenings. Compatibility is proved from
actual characteristic-section pullback, not assumed. The remaining
formal-functions comparison is not included in this theorem. -/
theorem actual_infinitesimal_nontrivial_idempotent {X : Scheme.{u}}
    (I : X.IdealSheafData) (S : Set I.subscheme) (hS : IsClopen S)
    (h0 : S ≠ ∅) (h1 : S ≠ Set.univ) :
    ∃ a : actualInfinitesimalSections I, a * a = a ∧ a ≠ 0 ∧ a ≠ 1 := by
  classical
  let SS (n : ℕ) : Set (actualPowerThickening I n) :=
    (actualPowerThickeningHomeomorph I n) ⁻¹' S
  have hc (n : ℕ) : IsClopen (SS n) :=
    hS.preimage (actualPowerThickeningHomeomorph I n).continuous
  have hcompat (m n : ℕ) (h : m ≤ n) :
      (actualPowerThickeningInclusion I h).appTop
        (actualClopenCharacteristic _ (SS n) (hc n)) =
          actualClopenCharacteristic _ (SS m) (hc m) := by
    have hs : (actualPowerThickeningInclusion I h) ⁻¹' SS n = SS m := by
      ext x
      change actualPowerThickeningHomeomorph I n
          (actualPowerThickeningInclusion I h x) ∈ S ↔
        actualPowerThickeningHomeomorph I m x ∈ S
      rw [actual_power_thickening_inclusion_point]
    rw [actual_clopen_characteristic_pullback]
    simp only [hs]
  let a : actualInfinitesimalSections I :=
    ⟨fun n => actualClopenCharacteristic _ (SS n) (hc n), hcompat⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · apply Subtype.ext
    funext n
    exact actual_clopen_characteristic_idempotent _ (SS n) (hc n)
  · intro ha
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h0
    let z := (actualPowerThickeningHomeomorph I 0).symm x
    have hz : z ∈ SS 0 := by simpa [SS, z] using hx
    have he := congrArg (fun b : actualInfinitesimalSections I =>
      (actualPowerThickening I 0).presheaf.Γgerm z (b.1 0)) ha
    simp [a, actual_clopen_characteristic_germ, hz] at he
  · intro ha
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr
      (show Sᶜ ≠ ∅ from fun h => h1 (Set.compl_empty_iff.mp h))
    let z := (actualPowerThickeningHomeomorph I 0).symm x
    have hz : z ∉ SS 0 := by simpa [SS, z] using hx
    have he := congrArg (fun b : actualInfinitesimalSections I =>
      (actualPowerThickening I 0).presheaf.Γgerm z (b.1 0)) ha
    simp [a, actual_clopen_characteristic_germ, hz] at he

end
end Negativity
