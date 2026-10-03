module

public import Negativity.ActualCechCohomologyExact
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualCechScaleZero (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens)
    (r : Γ(X, ⊤)) : actualCechZero X U →+ actualCechZero X U where
  toFun a j := actualSectionRestriction X le_top r * a j
  map_zero' := by funext j; exact mul_zero _
  map_add' a b := by funext j; exact mul_add _ _ _

def actualCechScaleOne (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens)
    (r : Γ(X, ⊤)) : actualCechOne X U →+ actualCechOne X U where
  toFun a j k := actualSectionRestriction X le_top r * a j k
  map_zero' := by funext j k; exact mul_zero _
  map_add' a b := by funext j k; exact mul_add _ _ _

theorem actual_cech_difference_scale (X : Scheme.{u}) {ι : Type v}
    (U : ι → X.Opens) (r : Γ(X, ⊤)) (a : actualCechZero X U) :
    actualCechDifference X U (actualCechScaleZero X U r a) =
      actualCechScaleOne X U r (actualCechDifference X U a) := by
  funext j k
  change actualSectionRestriction X inf_le_right
        (actualSectionRestriction X le_top r * a k) -
      actualSectionRestriction X inf_le_left
        (actualSectionRestriction X le_top r * a j) =
    actualSectionRestriction X le_top r *
      (actualSectionRestriction X inf_le_right (a k) -
        actualSectionRestriction X inf_le_left (a j))
  rw [map_mul, map_mul, actual_section_restriction_trans,
    actual_section_restriction_trans, mul_sub]

theorem actual_cech_boundary_scale (X : Scheme.{u}) {ι : Type v}
    (U : ι → X.Opens) (r : Γ(X, ⊤)) (a : actualCechOne X U) (j k l : ι) :
    actualCechBoundary X U (actualCechScaleOne X U r a) j k l =
      actualSectionRestriction X le_top r * actualCechBoundary X U a j k l := by
  change actualSectionRestriction X _ (actualSectionRestriction X le_top r * a k l) -
    actualSectionRestriction X _ (actualSectionRestriction X le_top r * a j l) +
    actualSectionRestriction X _ (actualSectionRestriction X le_top r * a j k) = _
  simp only [map_mul, actual_section_restriction_trans]
  change _ = actualSectionRestriction X le_top r * (_ - _ + _)
  ring

theorem actual_cech_pullback_scale_zero {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤)) (a : actualCechZero X U) :
    actualCechPullbackZero i U (actualCechScaleZero X U r a) =
      actualCechScaleZero Z (fun j => i ⁻¹ᵁ U j) (i.appTop r)
        (actualCechPullbackZero i U a) := by
  funext j
  change i.app (U j) (actualSectionRestriction X le_top r * a j) = _
  rw [map_mul, ← actual_section_restriction_naturality i le_top]
  rfl

theorem actual_cech_pullback_scale_one {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤)) (a : actualCechOne X U) :
    actualCechPullbackOne i U (actualCechScaleOne X U r a) =
      actualCechScaleOne Z (fun j => i ⁻¹ᵁ U j) (i.appTop r)
        (actualCechPullbackOne i U a) := by
  funext j k
  change i.app (U j ⊓ U k) (actualSectionRestriction X le_top r * a j k) = _
  rw [map_mul, ← actual_section_restriction_naturality i le_top]
  rfl

def actualClosedCechScaleKernel {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤)) :
    (actualCechPullbackZero i U).ker →+ (actualCechPullbackZero i U).ker :=
  ((actualCechScaleZero X U r).comp (actualCechPullbackZero i U).ker.subtype).codRestrict _
    (by intro a; change actualCechPullbackZero i U (actualCechScaleZero X U r a.1) = 0
        rw [actual_cech_pullback_scale_zero, a.2, map_zero])

def actualClosedCechScaleCycle {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤)) :
    actualClosedCechCocycles i U →+ actualClosedCechCocycles i U :=
  ((actualCechScaleOne X U r).comp (actualClosedCechCocycles i U).subtype).codRestrict _ (by
    intro a
    constructor
    · change actualCechPullbackOne i U (actualCechScaleOne X U r a.1) = 0
      rw [actual_cech_pullback_scale_one, a.2.1, map_zero]
    · change actualCechBoundary X U (actualCechScaleOne X U r a.1) = 0
      funext j k l
      rw [actual_cech_boundary_scale]
      have ha := congrArg (fun t : actualCechTwo X U => t j k l) a.2.2
      change actualCechBoundary X U a.1 j k l = 0 at ha
      rw [ha, mul_zero]
      rfl)

def actualClosedCechScalar {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤)) :
    actualClosedCechHOne i U →+ actualClosedCechHOne i U :=
  QuotientAddGroup.map (actualClosedCechBoundary i U).range
    (actualClosedCechBoundary i U).range (actualClosedCechScaleCycle i U r) (by
      rintro a ⟨c, rfl⟩
      refine ⟨actualClosedCechScaleKernel i U r c, ?_⟩
      apply Subtype.ext
      exact actual_cech_difference_scale X U r c.1)

/-- Final theorem: scalar multiplication by an actual global function
is well defined on actual first Cech cohomology of the actual ideal
kernel. Compatibility with the actual differentials and boundaries is
proved, not supplied. This constructs the scalar endomorphisms needed for
the subsequent graded Rees-module finite-generation theorem. -/
theorem actual_closed_cech_scalar_on_cocycles {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤))
    (a : actualClosedCechCocycles i U) :
    actualClosedCechScalar i U r (QuotientAddGroup.mk' _ a) =
      QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U r a) := rfl

end
end Negativity
