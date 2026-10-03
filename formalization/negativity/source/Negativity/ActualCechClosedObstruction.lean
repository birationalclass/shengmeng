module

public import Negativity.ActualCechClosedLifting
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualClosedCechCocycles {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) : AddSubgroup (actualCechOne X U) :=
  (actualCechPullbackOne i U).ker ⊓ (actualCechBoundary X U).ker

def actualClosedCechBoundary {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    (actualCechPullbackZero i U).ker →+ actualClosedCechCocycles i U :=
  ((actualCechDifference X U).comp (actualCechPullbackZero i U).ker.subtype).codRestrict
    (actualClosedCechCocycles i U) (by
      intro a
      constructor
      · change actualCechPullbackOne i U (actualCechDifference X U a.1) = 0
        rw [← actual_cech_pullback_difference, a.2, map_zero]
      · exact actual_cech_boundary_difference_zero X U a.1)

/-- Actual first Cech cohomology of the actual kernel of O_X -> i_* O_Z,
computed on the specified actual affine cover. Proper finiteness is not
asserted by this definition. -/
abbrev actualClosedCechHOne {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :=
  actualClosedCechCocycles i U ⧸ (actualClosedCechBoundary i U).range

def actualClosedCechLiftCocycle {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (b : Γ(Z, ⊤)) (a : actualCechZero X U)
    (ha : actualCechPullbackZero i U a =
      actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ U j) b) :
    actualClosedCechCocycles i U :=
  ⟨actualCechDifference X U a, by
    constructor
    · change actualCechPullbackOne i U (actualCechDifference X U a) = 0
      rw [← actual_cech_pullback_difference, ha]
      funext j k
      change actualSectionRestriction Z inf_le_right
          (actualSectionRestriction Z le_top b) -
        actualSectionRestriction Z inf_le_left (actualSectionRestriction Z le_top b) = 0
      rw [actual_section_restriction_trans, actual_section_restriction_trans, sub_self]
    · exact actual_cech_boundary_difference_zero X U a⟩

def actualClosedCechObstruction {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens)
    (b : Γ(Z, ⊤)) : actualClosedCechHOne i (fun j => (U j).1) :=
  QuotientAddGroup.mk' _ (actualClosedCechLiftCocycle i (fun j => (U j).1) b
    (actualClosedCechLocalLift i U b) (actual_closed_cech_local_lift_pullback i U b))

theorem actual_closed_cech_obstruction_independent_of_lifts {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens)
    (b : Γ(Z, ⊤)) (a : actualCechZero X (fun j => (U j).1))
    (ha : actualCechPullbackZero i (fun j => (U j).1) a =
      actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ (U j).1) b) :
    QuotientAddGroup.mk' _ (actualClosedCechLiftCocycle i (fun j => (U j).1) b a ha) =
      actualClosedCechObstruction i U b := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  let c : (actualCechPullbackZero i (fun j => (U j).1)).ker :=
    ⟨a - actualClosedCechLocalLift i U b, by
      change actualCechPullbackZero i (fun j => (U j).1)
        (a - actualClosedCechLocalLift i U b) = 0
      rw [map_sub, ha, actual_closed_cech_local_lift_pullback, sub_self]⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact map_sub (actualCechDifference X (fun j => (U j).1)) _ _

theorem actual_closed_cech_obstruction_zero_iff {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun j => (U j).1)) (b : Γ(Z, ⊤)) :
    actualClosedCechObstruction i U b = 0 ↔ ∃ s : Γ(X, ⊤), i.appTop s = b := by
  rw [actual_closed_cech_section_lifting_criterion i U hU b]
  change (actualClosedCechLiftCocycle i (fun j => (U j).1) b
    (actualClosedCechLocalLift i U b) (actual_closed_cech_local_lift_pullback i U b) :
      actualClosedCechHOne i (fun j => (U j).1)) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
  · rintro ⟨c, hc, hd⟩
    exact ⟨⟨c, hc⟩, Subtype.ext hd⟩

def actualClosedCechConnecting {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens) :
    Γ(Z, ⊤) →+ actualClosedCechHOne i (fun j => (U j).1) where
  toFun := actualClosedCechObstruction i U
  map_zero' := by
    have h := actual_closed_cech_obstruction_independent_of_lifts i U 0 0 (by
      rw [map_zero, map_zero])
    rw [← h]
    have hz : actualClosedCechLiftCocycle i (fun j => (U j).1) 0 0 (by
        rw [map_zero, map_zero]) = 0 :=
      Subtype.ext (map_zero (actualCechDifference X (fun j => (U j).1)))
    rw [hz, map_zero]
  map_add' b c := by
    have ha : actualCechPullbackZero i (fun j => (U j).1)
        (actualClosedCechLocalLift i U b + actualClosedCechLocalLift i U c) =
      actualCechGlobalRestriction Z (fun j => i ⁻¹ᵁ (U j).1) (b + c) := by
      rw [map_add, actual_closed_cech_local_lift_pullback,
        actual_closed_cech_local_lift_pullback, map_add]
    rw [← actual_closed_cech_obstruction_independent_of_lifts i U (b + c) _ ha]
    change QuotientAddGroup.mk' _ _ = QuotientAddGroup.mk' _ _ + QuotientAddGroup.mk' _ _
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact map_add (actualCechDifference X (fun j => (U j).1)) _ _

/-- Final theorem: the genuine connecting homomorphism to genuine kernel
Cech cohomology has kernel exactly the functions lifting from the ambient
scheme. Local lifts are constructed from actual affine surjectivity, and
their class is proved independent of choices. Proper graded cohomology
finiteness and a uniform transition bound remain separate geometric work. -/
theorem actual_closed_cech_connecting_exact {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun j => (U j).1)) :
    (actualClosedCechConnecting i U).ker = i.appTop.hom.toAddMonoidHom.range := by
  ext b
  change actualClosedCechObstruction i U b = 0 ↔ ∃ s, i.appTop s = b
  exact actual_closed_cech_obstruction_zero_iff i U hU b

end
end Negativity
