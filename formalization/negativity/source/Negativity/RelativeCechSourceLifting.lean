module
public import Negativity.RelativeCechSectionLifting
import Mathlib.Tactic
@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the actual cohomology kernel transition bound lifts
finite-thickening sections to actual source sections. The bound is explicit;
normality, birationality and a formal-functions comparison are not required. -/
theorem actual_relative_source_section_lifting_of_cech_kernel_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun k => (U k).1))
    (c : ℕ) (hvanish : ActualRelativeCechKernelVanishing f I U c) :
    ∀ n (b : Γ(actualRelativePowerThickening f I (n + c), ⊤)),
      ∃ s : Γ(X, ⊤), (actualRelativePowerInclusion f I (Nat.le_add_right n c) ≫
          ((I ^ (n + c + 1)).comap f).subschemeι).appTop s =
        (actualRelativePowerInclusion f I (Nat.le_add_right n c)).appTop b := by
  intro n b
  let j := actualRelativePowerInclusion f I (Nat.le_add_right n c)
  let i := ((I ^ (n + c + 1)).comap f).subschemeι
  have : IsClosedImmersion j := by
    dsimp [j, actualRelativePowerInclusion]
    infer_instance
  obtain ⟨s, hs⟩ := actual_closed_cech_lifting_of_cohomology_kernel_bound j i U hU
    (hvanish n) b
  exact ⟨s, hs⟩

end
end Negativity
