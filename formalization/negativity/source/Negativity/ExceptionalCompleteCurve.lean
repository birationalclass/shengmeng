module

public import Negativity.NonisolatedCompleteCurve
public import Negativity.FiniteNormalGeometry
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: every actual closed point over the exceptional center
of a proper birational morphism to a normal variety lies on an actual
complete contracted integral curve. The base field is algebraically closed
in arbitrary characteristic. All fiber and curve objects are constructed. -/
theorem exceptional_closed_point_complete_contracted_curve
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) (hxc : IsClosed ({x} : Set X))
    (hcenter : ∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U)) :
    ∃ (C : Scheme.{u}) (j : C ⟶ X), IsIntegral C ∧ Order.krullDim C = 1 ∧
      IsClosedImmersion j ∧ IsProper (j ≫ f ≫ b) ∧
      x ∈ Set.range j ∧ ∀ c : C, f (j c) = f x := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace b
  have hyc : IsClosed ({f x} : Set Y) := f.closedPoints_subset_preimage_closedPoints hxc
  have : IsClosedImmersion (Y.fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hyc
  let e := residueFieldIsoBase b (f x) hyc
  have hι : IsClosedImmersion (f.fiberι (f x)) :=
    inferInstanceAs (IsClosedImmersion (CategoryTheory.Limits.pullback.fst f
      (Y.fromSpecResidueField (f x))))
  have := hι
  let a : f.fiber (f x) ⟶ Spec (.of k) :=
    f.fiberToSpecResidueField (f x) ≫ Y.fromSpecResidueField (f x) ≫ b
  have ha : a = f.fiberToSpecResidueField (f x) ≫ Spec.map e.inv := by
    rw [SpecMap_residueFieldIsoBase_inv]
  have : IsProper (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd f
      (Y.fromSpecResidueField (f x))))
  have : IsProper a := by rw [ha]; infer_instance
  have hfc : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
    have he : f.fiberι (f x) ⁻¹' ({x} : Set X) = {f.asFiber x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun hz => (f.fiberι (f x)).isEmbedding.injective ?_, fun hz => ?_⟩
      · exact hz.trans (f.fiberι_asFiber x).symm
      · exact hz ▸ f.fiberι_asFiber x
    exact he ▸ hxc.preimage (f.fiberι (f x)).continuous
  obtain ⟨C, j, hC, hdC, hj, hp, hxj⟩ :=
    exists_complete_integral_curve_through_nonisolated_closed_point (f.fiber (f x)) k a
      (f.asFiber x) hfc (exceptional_fiber_point_not_isOpen_singleton f hf hn x hcenter)
  have := hj
  obtain ⟨c, hc⟩ := hxj
  refine ⟨C, j ≫ f.fiberι (f x), hC, hdC, inferInstance, ?_,
    ⟨c, ?_⟩, ?_⟩
  · have he : (j ≫ f.fiberι (f x)) ≫ f ≫ b = j ≫ a := by
      simp only [Category.assoc, Scheme.Hom.fiber_fac_assoc, a]
    exact he ▸ hp
  · simpa only [Scheme.Hom.comp_apply, hc] using f.fiberι_asFiber x
  · intro z
    have hz : f (f.fiberι (f x) (j z)) = f x := by
      have hm : f.fiberι (f x) (j z) ∈ f ⁻¹' {f x} := by
        rw [← f.range_fiberι (f x)]
        exact ⟨j z, rfl⟩
      exact Set.mem_singleton_iff.mp hm
    exact hz

end
end Negativity
