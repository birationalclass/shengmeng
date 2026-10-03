module

public import Negativity.ActualRelativeNef
public import Negativity.CartierOpenRestriction
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: relative nefness of an actual finite real Cartier
presentation restricts to every actual nonempty target open. Complete
curves, their actual contraction and their normalization/local-order
intersection are transported through the actual open immersion. No
intersection or contraction compatibility is an input. -/
theorem actual_relative_nef_on_target_open
    {X Y : Scheme.{u}} [IsIntegral X]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    (U : Y.Opens) [Nonempty (f ⁻¹ᵁ U)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (hn : ActualRelativeNef k (f ≫ b) f A r) :
    letI : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι
      ((f ⁻¹ᵁ U).isOpen.dense (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›))
    ActualRelativeNef k ((f ∣_ U) ≫ U.ι ≫ b) (f ∣_ U)
      (fun t => actualCartierPullback (f ⁻¹ᵁ U).ι (A t)) r := by
  let : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι
    ((f ⁻¹ᵁ U).isOpen.dense (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›))
  intro C _ hd g _ hc
  have hproper : IsProper ((g ≫ (f ⁻¹ᵁ U).ι) ≫ f ≫ b) := by
    rw [Category.assoc, ← Category.assoc (f ⁻¹ᵁ U).ι f b,
      ← morphismRestrict_ι, Category.assoc]
    infer_instance
  have hconst : ∀ x : C, ((g ≫ (f ⁻¹ᵁ U).ι) ≫ f) x =
      ((g ≫ (f ⁻¹ᵁ U).ι) ≫ f) (genericPoint C) := by
    intro x
    rw [Category.assoc, ← morphismRestrict_ι]
    exact congrArg (fun y => U.ι y) (hc x)
  have h := hn C hd (g ≫ (f ⁻¹ᵁ U).ι) hconst
  rw [complete_integral_curve_canonical_real_pullback_intersection hd k
    (g ≫ (f ∣_ U) ≫ U.ι ≫ b) (f ⁻¹ᵁ U).ι g A r]
  simpa only [Category.assoc, ← Category.assoc (f ⁻¹ᵁ U).ι f b,
    ← morphismRestrict_ι] using h

end
end Negativity
