module

public import Negativity.CompleteCurveAvoiding
public import Negativity.IntegralClosedSubscheme
public import Negativity.CurveSelection
public import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem connected_closed_subset_crossing_component
    (T : Type*) [TopologicalSpace T] [NoetherianSpace T] [ConnectedSpace T]
    (S : Set T) (hS : IsClosed S) (hne : S.Nonempty) (hnall : ¬ Set.univ ⊆ S) :
    ∃ F ∈ irreducibleComponents T, (F ∩ S).Nonempty ∧ ¬ F ⊆ S := by
  classical
  by_contra hn
  push Not at hn
  let A : Set (Set T) := {F | F ∈ irreducibleComponents T ∧ ¬ F ⊆ S}
  have hAfin : A.Finite := NoetherianSpace.finite_irreducibleComponents.subset
    (fun _ hF => hF.1)
  have hAc : IsClosed (⋃₀ A) := by
    rw [Set.sUnion_eq_biUnion]
    exact hAfin.isClosed_biUnion fun F hF => isClosed_of_mem_irreducibleComponents F hF.1
  have hAS : ⋃₀ A = Sᶜ := by
    ext x
    constructor
    · rintro ⟨F, hFA, hxF⟩ hxS
      exact hFA.2 (hn F hFA.1 ⟨x, hxF, hxS⟩)
    · intro hxS
      exact Set.mem_sUnion.mpr ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x,
          fun h => hxS (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
  have hopen : IsOpen S := by
    have hc : IsClosed Sᶜ := hAS ▸ hAc
    simpa using hc.isOpen_compl
  have heq : S = Set.univ := (IsClopen.eq_univ ⟨hS, hopen⟩ hne)
  exact hnall (by rw [heq])

/-- Final theorem: every nonempty proper closed subset of an actual
connected proper variety is met by an actual complete integral curve
not contained in that subset. The ambient scheme may be reducible or
nonreduced and of any dimension. Actual component, point, curve and
avoidance are all constructed; connectedness is the sole topological
hypothesis, not a curve-existence input. -/
theorem connected_complete_scheme_actual_crossing_curve
    (Z : Scheme.{u}) [ConnectedSpace Z] (k : Type u) [Field k] [IsAlgClosed k]
    (b : Z ⟶ Spec (.of k)) [IsProper b]
    (S : Set Z) (hS : IsClosed S) (hne : S.Nonempty) (hnall : ¬ Set.univ ⊆ S) :
    ∃ (C : Scheme.{u}) (j : C ⟶ Z), IsIntegral C ∧ Order.krullDim C = 1 ∧
      IsClosedImmersion j ∧ IsProper (j ≫ b) ∧
      (Set.range j ∩ S).Nonempty ∧ ¬ Set.range j ⊆ S := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian b
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian Z := ⟨⟩
  obtain ⟨F, hF, hFS, hFn⟩ := connected_closed_subset_crossing_component Z S hS hne hnall
  have hFc := isClosed_of_mem_irreducibleComponents F hF
  have hnot : ¬ F ∩ S ⊆ (∅ : Set Z) := by
    obtain ⟨x, hx⟩ := hFS
    exact fun h => h hx
  obtain ⟨x, hxFS, _, hxc⟩ := finiteType_exists_closedPoint_outside_support k Z b
    (F ∩ S) ∅ (hFc.inter hS) isClosed_empty hnot
  let Fc : Closeds Z := ⟨F, hFc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Fc
  let Y := I.subscheme
  let i : Y ⟶ Z := I.subschemeι
  obtain ⟨hY, hi, hr⟩ := closed_irreducible_actual_subscheme_properties Z Fc hF.1
  have := hY
  have := hi
  have hxrange : x ∈ Set.range i := by rw [hr]; exact hxFS.1
  obtain ⟨z, hz⟩ := hxrange
  have hzc : IsClosed ({z} : Set Y) := by
    have he : i ⁻¹' ({x} : Set Z) = {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hw => i.isEmbedding.injective (hw.trans hz.symm), fun hw => hw ▸ hz⟩
    exact he ▸ hxc.preimage i.continuous
  let T : Set Y := i ⁻¹' S
  have hT : IsClosed T := hS.preimage i.continuous
  have hηT : genericPoint Y ∉ T := by
    intro hm
    apply hFn
    intro y hy
    have hyr : y ∈ Set.range i := by rw [hr]; exact hy
    obtain ⟨w, rfl⟩ := hyr
    have hsp : i (genericPoint Y) ⤳ i w :=
      i.continuous.specialization_monotone ((genericPoint_spec Y).specializes trivial)
    exact hsp.mem_closed hS hm
  have hzT : z ∈ T := by
    change i z ∈ S
    rw [hz]
    exact hxFS.2
  have : IsProper (i ≫ b) := inferInstance
  obtain ⟨C, j, hC, hdC, hj, hp, hzj, havoid⟩ :=
    exists_complete_integral_curve_through_closed_point_avoiding Y k (i ≫ b) T hT hηT z hzc hzT
  have := hj
  obtain ⟨w, hw⟩ := hzj
  refine ⟨C, j ≫ i, hC, hdC, inferInstance,
    by simpa only [Category.assoc] using hp, ?_, ?_⟩
  · refine ⟨x, ⟨w, ?_⟩, hxFS.2⟩
    simpa only [Scheme.Hom.comp_apply, hw] using hz
  · intro hall
    apply havoid
    rintro _ ⟨c, rfl⟩
    exact hall ⟨c, by simp only [Scheme.Hom.comp_apply]⟩

end
end Negativity
