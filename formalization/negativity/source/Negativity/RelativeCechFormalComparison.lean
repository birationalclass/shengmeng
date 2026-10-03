module

public import Negativity.RelativeCechSectionLifting
public import Negativity.RelativeFormalInjectivity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

theorem actual_relative_power_inclusion_comp {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : Y.IdealSheafData) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    actualRelativePowerInclusion f I hlm ≫ actualRelativePowerInclusion f I hmn =
      actualRelativePowerInclusion f I (hlm.trans hmn) := by
  exact IdealSheafData.inclusion_comp _ _

/-- Final theorem, explicitly conditional: the actual first-cohomology
uniform kernel bound is the only supplied geometric bound needed for the
actual proper birational formal-functions comparison. Its injectivity and
uniform section-kernel bound are proved internally, and actual Cech
exactness and normal-base function descent construct the section lifts.
The cohomology bound hvanish remains unproved in the full application. -/
theorem actual_relative_formal_functions_bijective_of_cech_kernel_vanishing
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    [IsLocallyNoetherian Y] (k : Type u) [Field k] [PerfectField k]
    [Algebra k Γ(Y, ⊤)] [Algebra.FiniteType k Γ(Y, ⊤)]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun j => (U j).1))
    (c : ℕ) (hvanish : ActualRelativeCechKernelVanishing f I U c) :
    Function.Bijective (actualRelativeFormalFunctionsMap f I) := by
  obtain ⟨d, hd⟩ := actual_relative_kernel_uniform_bound k f hf I
  have hlift := actual_relative_section_lifting_of_cech_kernel_vanishing
    f hf hnY I U hU c hvanish
  apply actual_relative_formal_functions_bijective_of_uniform_approximation f I (d + c)
  · intro n r hr
    have he : n + (d + c) = (n + c) + d := by omega
    rw [he] at hr
    have hk := hd (n + c) hr
    exact (Ideal.pow_le_pow_right (show n + 1 ≤ n + c + 1 by omega)) hk
  · intro n b
    let h : n + c ≤ n + (d + c) := by omega
    let b' := (actualRelativePowerInclusion f I h).appTop b
    obtain ⟨r, hr⟩ := hlift n b'
    refine ⟨r, ?_⟩
    have ht := congrArg
      (fun g : actualRelativePowerThickening f I n ⟶
        actualRelativePowerThickening f I (n + (d + c)) => g.appTop b)
      (actual_relative_power_inclusion_comp f I (Nat.le_add_right n c) h)
    change (actualRelativePowerInclusion f I (Nat.le_add_right n c)).appTop b' = _ at ht
    exact hr.trans ht

end
end Negativity
