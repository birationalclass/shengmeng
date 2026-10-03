module

public import Negativity.ActualCechScalars
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

instance actualClosedCechModule {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    Module Γ(X, ⊤) (actualClosedCechHOne i U) where
  smul r q := actualClosedCechScalar i U r q
  one_smul q := by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U 1 a) =
        QuotientAddGroup.mk' _ a
      apply congrArg (QuotientAddGroup.mk' (actualClosedCechBoundary i U).range)
      apply Subtype.ext
      funext j k
      change actualSectionRestriction X le_top 1 * a.1 j k = a.1 j k
      rw [map_one, one_mul]
  mul_smul r s q := by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U (r * s) a) =
        QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U r
          (actualClosedCechScaleCycle i U s a))
      apply congrArg (QuotientAddGroup.mk' (actualClosedCechBoundary i U).range)
      apply Subtype.ext
      funext j k
      change actualSectionRestriction X le_top (r * s) * a.1 j k =
        actualSectionRestriction X le_top r * (actualSectionRestriction X le_top s * a.1 j k)
      rw [map_mul, mul_assoc]
  smul_zero r := map_zero (actualClosedCechScalar i U r)
  smul_add r q p := map_add (actualClosedCechScalar i U r) q p
  add_smul r s q := by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U (r + s) a) =
        QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U r a) +
        QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U s a)
      rw [← map_add]
      apply congrArg (QuotientAddGroup.mk' (actualClosedCechBoundary i U).range)
      apply Subtype.ext
      funext j k
      change actualSectionRestriction X le_top (r + s) * a.1 j k =
        actualSectionRestriction X le_top r * a.1 j k +
          actualSectionRestriction X le_top s * a.1 j k
      rw [map_add, add_mul]
  zero_smul q := by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U 0 a) = 0
      have hz : actualClosedCechScaleCycle i U 0 a = 0 := by
        apply Subtype.ext
        funext j k
        change actualSectionRestriction X le_top 0 * a.1 j k = 0
        rw [map_zero, zero_mul]
      rw [hz, map_zero]

/-- Final theorem: actual kernel first Cech cohomology carries an actual
global-section module structure. All module axioms are proved for the
constructed scalar maps, and the action on a genuine cocycle is restriction
of the global scalar followed by multiplication. No module action or
proper finite-generation claim is supplied as an input. -/
theorem actual_closed_cech_module_action {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (r : Γ(X, ⊤))
    (a : actualClosedCechCocycles i U) :
    r • QuotientAddGroup.mk' (actualClosedCechBoundary i U).range a =
      QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U r a) := rfl

end
end Negativity
