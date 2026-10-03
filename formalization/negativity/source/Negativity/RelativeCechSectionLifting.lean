module

public import Negativity.ActualCechKernelLifting
public import Negativity.RelativeFormalApproximation
public import Negativity.ProperBirationalSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def ActualRelativeCechKernelVanishing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens) (c : ℕ) : Prop :=
  ∀ n (q : actualClosedCechHOne ((I ^ (n + c + 1)).comap f).subschemeι
      (fun k => (U k).1)),
    actualClosedCechForget ((I ^ (n + c + 1)).comap f).subschemeι
      (fun k => (U k).1) q = 0 →
    actualClosedCechHOneTransition (actualRelativePowerInclusion f I (Nat.le_add_right n c))
      ((I ^ (n + c + 1)).comap f).subschemeι (fun k => (U k).1) q = 0

/-- Final theorem, explicitly conditional: a uniform actual Cech
cohomology kernel-vanishing bound gives the actual section-image bound
over a normal affine base. Actual closed immersions, exactness and
transition naturality provide the lift to X; the proved actual proper
structure-sheaf theorem descends it to Y. The stated cohomology bound is
still open and is not replaced by an abstract supplied section map. -/
theorem actual_relative_section_lifting_of_cech_kernel_vanishing
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (hf : BirationalMorphism f) (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun k => (U k).1))
    (c : ℕ) (hvanish : ActualRelativeCechKernelVanishing f I U c) :
    ∀ n (b : Γ(actualRelativePowerThickening f I (n + c), ⊤)),
      ∃ r : Γ(Y, ⊤), actualRelativeRestriction f I n r =
        (actualRelativePowerInclusion f I (Nat.le_add_right n c)).appTop b := by
  intro n b
  let j := actualRelativePowerInclusion f I (Nat.le_add_right n c)
  let i := ((I ^ (n + c + 1)).comap f).subschemeι
  have hi : j ≫ i = ((I ^ (n + 1)).comap f).subschemeι :=
    IdealSheafData.inclusion_subschemeι _
  have : IsClosedImmersion j := by
    dsimp [j, actualRelativePowerInclusion]
    infer_instance
  obtain ⟨s, hs⟩ := actual_closed_cech_lifting_of_cohomology_kernel_bound j i U hU
    (hvanish n) b
  obtain ⟨r, hrTop⟩ := (proper_normal_birational_open_functions_bijective f hf hnY ⊤).2 s
  have hr : f.appTop r = s := hrTop
  have ht := (congrArg (fun a : Γ(X, ⊤) => (j ≫ i).appTop a) hr).trans hs
  rw [hi] at ht
  exact ⟨r, ht⟩

end
end Negativity
