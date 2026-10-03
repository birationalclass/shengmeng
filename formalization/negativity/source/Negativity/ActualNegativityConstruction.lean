module

public import Negativity.ActualNegativityWitness
public import Negativity.EffectiveExceptionalWitness
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual negativity over an affine normal base, with
only a supplied actual strictly anti-positive Cartier divisor. Its effective
principal twist E and its exceptional coverage are constructed internally.
The maximum-ratio argument, actual curves and actual normalized intersections
are all proved. The remaining geometric input is existence of this
anti-positive Cartier divisor from projectivity and ample positivity.
This theorem therefore does not claim the full projective negativity lemma. -/
theorem actual_negativity_of_strictly_negative_cartier
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
    (A₀ : CartierAtlas X ι)
    (hanti : ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
      (j : C ⟶ X) [IsProper (j ≫ f ≫ b)], IsClosedImmersion j →
      (∀ c : C, f (j c) = f (j (genericPoint C))) →
      normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j A₀ < 0) :
    ∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ) := by
  classical
  obtain ⟨s, hE, hcover⟩ := exists_effective_exceptional_covering_cartier_twist
    k b f hf hnX hnY A₀ hanti
  let E := A₀.rationalTwist s
  let AA : Sum τ Unit → CartierAtlas X ι := Sum.elim A (fun _ => E)
  let dd : Sum τ Unit → ℝ := Sum.elim d (fun _ => 0)
  let ee : Sum τ Unit → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hcyc : (∑ t, (AA t).weightedWeilCycle hnX (dd t)) =
      ∑ t, (A t).weightedWeilCycle hnX (d t) := by
    rw [Fintype.sum_sum_type]
    have hz : E.weightedWeilCycle hnX 0 = 0 := by
      ext x
      simp [CartierAtlas.weightedWeilCycle]
    simpa [AA, dd] using (show
      (∑ t, (A t).weightedWeilCycle hnX (d t)) + E.weightedWeilCycle hnX 0 =
        ∑ t, (A t).weightedWeilCycle hnX (d t) by rw [hz, add_zero])
  have hpush' : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (AA t).weightedWeilCycle hnX (dd t))) := by
    rwa [hcyc]
  have hnef' : ActualRelativeNef k (f ≫ b) f AA (fun t => -dd t) := by
    intro C _ hd j _ hc
    simpa [normalizedRealCartierCurveIntersection, AA, dd, Fintype.sum_sum_type]
      using hnef C hd j hc
  have heff : ∀ x : X, 0 ≤ ∑ t, ee t * ((AA t).coefficient hnX x : ℝ) := by
    intro x
    have hn : 0 ≤ E.coefficient hnX x :=
      effective_cartierAtlas_weil_nonneg X hnX E hE x
    simpa [AA, ee, Fintype.sum_sum_type] using
      (show (0 : ℝ) ≤ (E.coefficient hnX x : ℝ) by exact_mod_cast hn)
  have hecover : ∀ x : X, Order.coheight x = 1 →
      (∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U)) →
      0 < ∑ t, ee t * ((AA t).coefficient hnX x : ℝ) := by
    intro x hx hc
    simpa [AA, ee, Fintype.sum_sum_type] using
      (show (0 : ℝ) < (E.coefficient hnX x : ℝ) by exact_mod_cast hcover x hx hc)
  have hEanti : ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
      (j : C ⟶ X) [IsProper (j ≫ f ≫ b)], IsClosedImmersion j →
      (∀ c : C, f (j c) = f (j (genericPoint C))) →
      normalizedRealCartierCurveIntersection hd k (j ≫ f ≫ b) j AA ee < 0 := by
    intro C _ hd j _ hj hc
    have hi := complete_integral_curve_ambient_cartier_principal_invariance
      hd k (j ≫ f ≫ b) j A₀ s
    have he : normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j E < 0 := by
      rw [hi]
      exact hanti C hd j hj hc
    simpa [normalizedRealCartierCurveIntersection, AA, ee, Fintype.sum_sum_type]
      using (show (normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j E : ℝ) < 0 by
        exact_mod_cast he)
  have hall := actual_negativity_of_antiample_witness k b f hf hnX hnY
    AA dd ee hpush' hnef' heff hecover hEanti
  intro x
  simpa [AA, dd, Fintype.sum_sum_type] using hall x

end
end Negativity
