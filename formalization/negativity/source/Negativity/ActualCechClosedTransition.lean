module

public import Negativity.ActualCechClosedObstruction
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualClosedCechKernelTransition {X Z W : Scheme.{u}}
    (j : W ⟶ Z) (i : Z ⟶ X) {ι : Type v} (U : ι → X.Opens) :
    (actualCechPullbackZero i U).ker →+
      (actualCechPullbackZero (j ≫ i) U).ker where
  toFun a := ⟨a.1, by
    funext k
    change (j ≫ i).app (U k) (a.1 k) = 0
    rw [Scheme.Hom.comp_app, ConcreteCategory.comp_apply]
    have ha := congrArg (fun t : actualCechZero Z (fun k => i ⁻¹ᵁ U k) => t k) a.2
    change i.app (U k) (a.1 k) = 0 at ha
    rw [ha, map_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def actualClosedCechCycleTransition {X Z W : Scheme.{u}}
    (j : W ⟶ Z) (i : Z ⟶ X) {ι : Type v} (U : ι → X.Opens) :
    actualClosedCechCocycles i U →+ actualClosedCechCocycles (j ≫ i) U where
  toFun a := ⟨a.1, by
    constructor
    · funext k l
      change (j ≫ i).app (U k ⊓ U l) (a.1 k l) = 0
      rw [Scheme.Hom.comp_app, ConcreteCategory.comp_apply]
      have ha := congrArg
        (fun t : actualCechOne Z (fun k => i ⁻¹ᵁ U k) => t k l) a.2.1
      change i.app (U k ⊓ U l) (a.1 k l) = 0 at ha
      rw [ha, map_zero]
    · exact a.2.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def actualClosedCechHOneTransition {X Z W : Scheme.{u}}
    (j : W ⟶ Z) (i : Z ⟶ X) {ι : Type v} (U : ι → X.Opens) :
    actualClosedCechHOne i U →+ actualClosedCechHOne (j ≫ i) U :=
  QuotientAddGroup.map (actualClosedCechBoundary i U).range
    (actualClosedCechBoundary (j ≫ i) U).range (actualClosedCechCycleTransition j i U) (by
      rintro a ⟨c, rfl⟩
      exact ⟨actualClosedCechKernelTransition j i U c, rfl⟩)

/-- Final theorem: the actual connecting obstruction commutes with the
actual map between closed subschemes. Its first-cohomology transition is
constructed from the inclusion of actual kernels and actual boundaries;
no naturality square is supplied as a hypothesis. This does not prove the
uniform proper cohomology bound needed for eventual lifting. -/
theorem actual_closed_cech_connecting_naturality {X Z W : Scheme.{u}}
    (j : W ⟶ Z) (i : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    {ι : Type v} (U : ι → X.affineOpens) (b : Γ(Z, ⊤)) :
    actualClosedCechHOneTransition j i (fun k => (U k).1)
      (actualClosedCechConnecting i U b) =
        actualClosedCechConnecting (j ≫ i) U (j.appTop b) := by
  let a := actualClosedCechLocalLift i U b
  have ha : actualCechPullbackZero (j ≫ i) (fun k => (U k).1) a =
      actualCechGlobalRestriction W (fun k => (j ≫ i) ⁻¹ᵁ (U k).1) (j.appTop b) := by
    funext k
    change (j ≫ i).app (U k).1 (a k) =
      actualSectionRestriction W le_top (j.appTop b)
    rw [Scheme.Hom.comp_app, ConcreteCategory.comp_apply]
    have hi := congrArg (fun t : actualCechZero Z (fun k => i ⁻¹ᵁ (U k).1) => t k)
      (actual_closed_cech_local_lift_pullback i U b)
    change i.app (U k).1 (a k) = actualSectionRestriction Z le_top b at hi
    rw [hi]
    exact (actual_section_restriction_naturality j le_top b).symm
  change _ = actualClosedCechObstruction (j ≫ i) U (j.appTop b)
  rw [← actual_closed_cech_obstruction_independent_of_lifts (j ≫ i) U (j.appTop b) a ha]
  rfl

end
end Negativity
