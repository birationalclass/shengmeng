module

public import Negativity.ActualNegativityAffineSections
public import Negativity.ProjPolynomialSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: actual real-Cartier negativity (1) over an affine
normal base with an actual closed embedding into standard relative
projective space. The geometric O(1) Cartier divisor, coordinate
sections, positive curve degree, effective exceptional E and its coverage
are all constructed internally. Neither numerical positivity nor any
Cartier/section/E witness is supplied. The ambient real Cartier chart
index may be arbitrary. Global affine-base gluing and the proper Chow
reduction are separate theorems still needed for the full main result. -/
theorem actual_projective_affine_negativity
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hpush : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (A t).weightedWeilCycle hnX (d t))))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t))
    (n : ℕ)
    (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(Y, ⊤)))
    [IsClosedImmersion j] :
    ∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ) := by
  classical
  obtain ⟨A₀, ⟨S⟩⟩ := exists_actual_projective_space_cartier_sections Γ(Y, ⊤) n j
  let AA (t : τ) := (A t).pointIndexed
  have hcyc : (∑ t, (AA t).weightedWeilCycle hnX (d t)) =
      ∑ t, (A t).weightedWeilCycle hnX (d t) := by
    apply Finset.sum_congr rfl
    intro t _
    ext x
    simp [AA, CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle,
      cartierAtlas_pointIndexed_coefficient]
  have hp : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (AA t).weightedWeilCycle hnX (d t))) := by rwa [hcyc]
  have hn : ActualRelativeNef k (f ≫ b) f AA (fun t => -d t) := by
    intro C _ hd g _ hc
    rw [complete_integral_curve_real_cartier_presentation_independent hnX hd k
      (g ≫ f ≫ b) g AA A (fun t => -d t) (fun t => -d t)
      (by intro x; simp [AA, cartierAtlas_pointIndexed_coefficient])]
    exact hnef C hd g hc
  have hall := actual_negativity_of_affine_section_cover k b f hf hnX hnY
    AA d hp hn A₀ S
  intro x
  simpa [AA, cartierAtlas_pointIndexed_coefficient] using hall x

end
end Negativity
