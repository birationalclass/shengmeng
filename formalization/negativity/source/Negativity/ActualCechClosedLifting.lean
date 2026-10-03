module

public import Negativity.ActualCechSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_section_restriction_naturality {X Z : Scheme.{u}} (i : Z ⟶ X)
    {U V : X.Opens} (h : U ≤ V) (s : Γ(X, V)) :
    actualSectionRestriction Z (i.preimage_mono h) (i.app V s) =
      i.app U (actualSectionRestriction X h s) := by
  exact congrArg (fun g : Γ(X, V) ⟶ Γ(Z, i ⁻¹ᵁ U) => g s)
    (i.naturality (homOfLE h).op).symm

def actualCechPullbackZero {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    actualCechZero X U →+ actualCechZero Z (fun j => i ⁻¹ᵁ U j) where
  toFun a j := i.app (U j) (a j)
  map_zero' := by funext j; exact map_zero _
  map_add' a b := by funext j; exact map_add _ _ _

def actualCechPullbackOne {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    actualCechOne X U →+ actualCechOne Z (fun j => i ⁻¹ᵁ U j) where
  toFun a j k := i.app (U j ⊓ U k) (a j k)
  map_zero' := by funext j k; exact map_zero _
  map_add' a b := by funext j k; exact map_add _ _ _

theorem actual_cech_pullback_difference {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (a : actualCechZero X U) :
    actualCechDifference Z (fun j => i ⁻¹ᵁ U j) (actualCechPullbackZero i U a) =
      actualCechPullbackOne i U (actualCechDifference X U a) := by
  funext j k
  change actualSectionRestriction Z _ (i.app (U k) (a k)) -
    actualSectionRestriction Z _ (i.app (U j) (a j)) =
      i.app (U j ⊓ U k)
        (actualSectionRestriction X inf_le_right (a k) -
          actualSectionRestriction X inf_le_left (a j))
  rw [actual_section_restriction_naturality i inf_le_right,
    actual_section_restriction_naturality i inf_le_left, map_sub]

def actualClosedCechLocalLift {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens)
    (b : Γ(Z, ⊤)) : actualCechZero X (fun j => (U j).1) :=
  fun j => Classical.choose (i.app_surjective (U j).1 (U j).2
    (actualSectionRestriction Z le_top b))

theorem actual_closed_cech_local_lift_pullback {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {ι : Type v}
    (U : ι → X.affineOpens) (b : Γ(Z, ⊤)) :
    actualCechPullbackZero i (fun j => (U j).1) (actualClosedCechLocalLift i U b) =
      actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ (U j).1) b := by
  funext j
  exact Classical.choose_spec (i.app_surjective (U j).1 (U j).2
    (actualSectionRestriction Z le_top b))

/-- Final theorem: for an actual closed immersion and actual affine open
cover, a global function on the closed subscheme lifts precisely when the
actual differences of its constructed local lifts are a boundary of
sections in the actual kernel. Thus the gluing obstruction is concrete;
no presumed Cech exactness or cohomology-lifting hypothesis is supplied. -/
theorem actual_closed_cech_section_lifting_criterion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {ι : Type v}
    (U : ι → X.affineOpens) (hU : (⊤ : X.Opens) ≤ iSup (fun j => (U j).1))
    (b : Γ(Z, ⊤)) :
    (∃ s : Γ(X, ⊤), i.appTop s = b) ↔
      ∃ c : actualCechZero X (fun j => (U j).1),
        actualCechPullbackZero i (fun j => (U j).1) c = 0 ∧
        actualCechDifference X (fun j => (U j).1) c =
          actualCechDifference X (fun j => (U j).1) (actualClosedCechLocalLift i U b) := by
  let V := fun j => (U j).1
  let a := actualClosedCechLocalLift i U b
  let d := actualCechDifference X V
  let p := actualCechPullbackZero i V
  have ha : p a = actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ V j) b :=
    actual_closed_cech_local_lift_pullback i U b
  have hp (s : Γ(X, ⊤)) :
      p (actualCechGlobalRestriction X V s) =
        actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ V j) (i.appTop s) := by
    funext j
    exact (actual_section_restriction_naturality i le_top s).symm
  have hg (s : Γ(X, ⊤)) : d (actualCechGlobalRestriction X V s) = 0 := by
    exact (actual_cech_global_sections_exact X V hU).le ⟨s, rfl⟩
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨a - actualCechGlobalRestriction X V s, ?_, ?_⟩
    · change p (a - actualCechGlobalRestriction X V s) = 0
      rw [map_sub, hp, hs, ha, sub_self]
    · change d (a - actualCechGlobalRestriction X V s) = d a
      rw [map_sub, hg, sub_zero]
  · rintro ⟨c, hc, hd⟩
    have hdiff : d (a - c) = 0 := by
      rw [map_sub, hd, sub_self]
    have hrange : a - c ∈ AddMonoidHom.range (actualCechGlobalRestriction X V) := by
      rw [actual_cech_global_sections_exact X V hU]
      exact hdiff
    obtain ⟨s, hs⟩ := hrange
    refine ⟨s, ?_⟩
    have hlocal : actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ V j) (i.appTop s) =
        actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ V j) b := by
      rw [← hp, hs, map_sub, hc, sub_zero, ha]
    have hcover : (⊤ : Z.Opens) ≤ iSup (fun j => i ⁻¹ᵁ V j) := by
      rw [← i.preimage_iSup]
      exact i.preimage_mono hU
    obtain ⟨t, _ht, htuniq⟩ := Z.sheaf.existsUnique_gluing' (fun j => i ⁻¹ᵁ V j)
      ⊤ (fun _ => homOfLE le_top) hcover
      (fun j => actualSectionRestriction Z le_top b) (by
        intro j k
        exact (actual_section_restriction_trans Z inf_le_left le_top b).trans
          (actual_section_restriction_trans Z inf_le_right le_top b).symm)
    exact (htuniq _ (fun j => congrArg (fun x => x j) hlocal)).trans
      (htuniq _ (fun _ => rfl)).symm

end
end Negativity
