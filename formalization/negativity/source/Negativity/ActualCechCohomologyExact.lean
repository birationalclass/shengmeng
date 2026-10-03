module

public import Negativity.ActualCechClosedTransition
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualCechCocycles (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    AddSubgroup (actualCechOne X U) := (actualCechBoundary X U).ker

def actualCechCoboundary (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    actualCechZero X U →+ actualCechCocycles X U :=
  (actualCechDifference X U).codRestrict (actualCechCocycles X U)
    (fun a => actual_cech_boundary_difference_zero X U a)

abbrev actualCechHOne (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :=
  actualCechCocycles X U ⧸ (actualCechCoboundary X U).range

def actualClosedCechForgetCycle {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    actualClosedCechCocycles i U →+ actualCechCocycles X U where
  toFun a := ⟨a.1, a.2.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def actualClosedCechForget {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    actualClosedCechHOne i U →+ actualCechHOne X U :=
  QuotientAddGroup.map (actualClosedCechBoundary i U).range
    (actualCechCoboundary X U).range (actualClosedCechForgetCycle i U) (by
      rintro a ⟨c, rfl⟩
      exact ⟨c.1, rfl⟩)

/-- Final theorem: the next term of the actual Cech cohomology exact
sequence is proved on the actual affine cover. The image of the actual
closed-subscheme connecting map equals the kernel of actual kernel
cohomology -> ambient cohomology. No long-exact-sequence premise is given.
The proper finite-generation theorem for these graded cohomology modules
is still a separate geometric requirement. -/
theorem actual_closed_cech_cohomology_exact {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun j => (U j).1)) :
    (actualClosedCechConnecting i U).range =
      (actualClosedCechForget i (fun j => (U j).1)).ker := by
  let V := fun j => (U j).1
  ext q
  constructor
  · rintro ⟨b, rfl⟩
    change actualClosedCechForget i V (actualClosedCechObstruction i U b) = 0
    change ((actualClosedCechForgetCycle i V
      (actualClosedCechLiftCocycle i V b (actualClosedCechLocalLift i U b)
        (actual_closed_cech_local_lift_pullback i U b))) : actualCechHOne X V) = 0
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨actualClosedCechLocalLift i U b, rfl⟩
  · intro hq
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    change ((actualClosedCechForgetCycle i V z) : actualCechHOne X V) = 0 at hq
    obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hq
    have hd : actualCechDifference X V a = z.1 := congrArg Subtype.val ha
    have hp : actualCechDifference Z (fun j => i ⁻¹ᵁ V j)
        (actualCechPullbackZero i V a) = 0 := by
      rw [actual_cech_pullback_difference, hd]
      exact z.2.1
    have hcover : (⊤ : Z.Opens) ≤ iSup (fun j => i ⁻¹ᵁ V j) := by
      rw [← i.preimage_iSup]
      exact i.preimage_mono hU
    have hg : actualCechPullbackZero i V a ∈
        (actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ V j)).range := by
      rw [actual_cech_global_sections_exact Z (fun j => i ⁻¹ᵁ V j) hcover]
      exact hp
    obtain ⟨b, hb⟩ := hg
    refine ⟨b, ?_⟩
    change actualClosedCechObstruction i U b = (z : actualClosedCechHOne i V)
    rw [← actual_closed_cech_obstruction_independent_of_lifts i U b a hb.symm]
    exact congrArg (QuotientAddGroup.mk' (actualClosedCechBoundary i V).range)
      (show actualClosedCechLiftCocycle i V b a hb.symm = z from Subtype.ext hd)

end
end Negativity
