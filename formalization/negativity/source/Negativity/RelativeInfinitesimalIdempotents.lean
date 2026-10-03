module

public import Negativity.RelativeFormalFunctionsMap
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

/-- Every relative power thickening has the same actual underlying closed
subspace, even when the source is nonaffine. -/
def actualRelativePowerHomeomorph {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (n : ℕ) :
    actualRelativePowerThickening f I n ≃ₜ (I.comap f).subscheme :=
  Homeomorph.setCongr (congrArg SetLike.coe (by
    rw [IdealSheafData.support_comap, IdealSheafData.support_pow_succ,
      IdealSheafData.support_comap]))

theorem actual_relative_power_inclusion_point {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : Y.IdealSheafData) {m n : ℕ} (h : m ≤ n)
    (x : actualRelativePowerThickening f I m) :
    actualRelativePowerHomeomorph f I n (actualRelativePowerInclusion f I h x) =
      actualRelativePowerHomeomorph f I m x := by
  apply Subtype.ext
  exact congrArg (fun g => g x) (IdealSheafData.inclusion_subschemeι
    (IdealSheafData.comap_mono f (show I ^ (n + 1) ≤ I ^ (m + 1) from by
      intro U
      simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
        (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.add_le_add_right h 1)))))

theorem actual_compatible_clopen_nontrivial_idempotent
    (Z : ℕ → Scheme.{u}) (F : Scheme.{u})
    (inc : ∀ {m n : ℕ}, m ≤ n → (Z m ⟶ Z n))
    (e : ∀ n, Z n ≃ₜ F)
    (he : ∀ m n (h : m ≤ n) (x : Z m), e n (inc h x) = e m x)
    (S : Set F)
    (hS : IsClopen S) (h0 : S ≠ ∅) (h1 : S ≠ Set.univ) :
    ∃ a : actualCompatibleSchemeSections Z inc, a * a = a ∧ a ≠ 0 ∧ a ≠ 1 := by
  classical
  let SS (n : ℕ) : Set (Z n) := (e n) ⁻¹' S
  have hc (n : ℕ) : IsClopen (SS n) := hS.preimage (e n).continuous
  have hcompat (m n : ℕ) (h : m ≤ n) :
      (inc h).appTop
        (actualClopenCharacteristic _ (SS n) (hc n)) =
          actualClopenCharacteristic _ (SS m) (hc m) := by
    have hs : (inc h) ⁻¹' SS n = SS m := by
      ext x
      change e n (inc h x) ∈ S ↔ e m x ∈ S
      rw [he]
    rw [actual_clopen_characteristic_pullback]
    simp only [hs]
  let a : actualCompatibleSchemeSections Z inc :=
    ⟨fun n => actualClopenCharacteristic _ (SS n) (hc n), hcompat⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · apply Subtype.ext
    funext n
    exact actual_clopen_characteristic_idempotent _ (SS n) (hc n)
  · intro ha
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h0
    let z := (e 0).symm x
    have hz : z ∈ SS 0 := by simpa [SS, z] using hx
    have hh := congrArg (fun b : actualCompatibleSchemeSections Z inc =>
      (Z 0).presheaf.Γgerm z (b.1 0)) ha
    simp [a, actual_clopen_characteristic_germ, hz] at hh
  · intro ha
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr
      (show Sᶜ ≠ ∅ from fun h => h1 (Set.compl_empty_iff.mp h))
    let z := (e 0).symm x
    have hz : z ∉ SS 0 := by simpa [SS, z] using hx
    have hh := congrArg (fun b : actualCompatibleSchemeSections Z inc =>
      (Z 0).presheaf.Γgerm z (b.1 0)) ha
    simp [a, actual_clopen_characteristic_germ, hz] at hh

/-- Final theorem: a nontrivial clopen decomposition of the actual closed
inverse-image scheme constructs a nontrivial idempotent in the genuine
relative infinitesimal function limit. The source need not be affine.
The proof uses actual characteristic sections and actual scheme inclusions;
no limit element or compatibility relation is taken as an input. -/
theorem actual_relative_infinitesimal_nontrivial_idempotent {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : Y.IdealSheafData) (S : Set (I.comap f).subscheme)
    (hS : IsClopen S) (h0 : S ≠ ∅) (h1 : S ≠ Set.univ) :
    ∃ a : actualRelativeInfinitesimalSections f I, a * a = a ∧ a ≠ 0 ∧ a ≠ 1 :=
  actual_compatible_clopen_nontrivial_idempotent
    (actualRelativePowerThickening f I) (I.comap f).subscheme
    (fun h => actualRelativePowerInclusion f I h) (actualRelativePowerHomeomorph f I)
    (fun _ _ h x => actual_relative_power_inclusion_point f I h x) S hS h0 h1

end
end Negativity
