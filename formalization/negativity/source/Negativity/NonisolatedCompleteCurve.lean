module

public import Negativity.IntegralClosedSubscheme
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem nonisolated_point_positive_irreducible_component
    (T : Type*) [TopologicalSpace T] [NoetherianSpace T]
    (x : T) (hx : ¬ IsOpen ({x} : Set T)) :
    ∃ F ∈ irreducibleComponents T, x ∈ F ∧ ¬ F ⊆ {x} := by
  classical
  by_contra h
  push Not at h
  let S : Set (Set T) := {F | F ∈ irreducibleComponents T ∧ x ∉ F}
  have hsfin : S.Finite := NoetherianSpace.finite_irreducibleComponents.subset
    (fun _ hF => hF.1)
  have hsc : IsClosed (⋃₀ S) := by
    rw [Set.sUnion_eq_biUnion]
    exact hsfin.isClosed_biUnion fun F hF => isClosed_of_mem_irreducibleComponents F hF.1
  have heq : (⋃₀ S)ᶜ = ({x} : Set T) := by
    ext y
    constructor
    · intro hy
      by_contra hne
      have hxy : y ≠ x := by simpa only [Set.mem_singleton_iff] using hne
      have hFx : x ∉ irreducibleComponent y := by
        intro hxF
        exact hxy (h _ (irreducibleComponent_mem_irreducibleComponents y) hxF
          mem_irreducibleComponent)
      exact hy (Set.mem_sUnion.mpr ⟨irreducibleComponent y,
        ⟨irreducibleComponent_mem_irreducibleComponents y, hFx⟩, mem_irreducibleComponent⟩)
    · rintro rfl
      rintro ⟨F, hFS, hxF⟩
      exact hFS.2 hxF
  exact hx (heq ▸ hsc.isOpen_compl)

/-- Final theorem: every nonisolated closed point of an actual complete
finite-type scheme over an algebraically closed field lies on a closed
complete integral curve. The ambient scheme may be reducible and nonreduced;
the positive-dimensional component and its reduced structure are constructed. -/
theorem exists_complete_integral_curve_through_nonisolated_closed_point
    (Z : Scheme.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (b : Z ⟶ Spec (.of k)) [IsProper b]
    (x : Z) (hxc : IsClosed ({x} : Set Z)) (hxo : ¬ IsOpen ({x} : Set Z)) :
    ∃ (C : Scheme.{u}) (j : C ⟶ Z), IsIntegral C ∧ Order.krullDim C = 1 ∧
      IsClosedImmersion j ∧ IsProper (j ≫ b) ∧ x ∈ Set.range j := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian b
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian Z := ⟨⟩
  obtain ⟨F, hF, hxF, hFn⟩ := nonisolated_point_positive_irreducible_component Z x hxo
  let Fc : Closeds Z := ⟨F, isClosed_of_mem_irreducibleComponents F hF⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Fc
  let Y := I.subscheme
  let i : Y ⟶ Z := I.subschemeι
  obtain ⟨hY, hi, hr⟩ := closed_irreducible_actual_subscheme_properties Z Fc hF.1
  have := hY
  have := hi
  have hxrange : x ∈ Set.range i := by rw [hr]; exact hxF
  obtain ⟨z, hz⟩ := hxrange
  have hzc : IsClosed ({z} : Set Y) := by
    have he : i ⁻¹' ({x} : Set Z) = {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hw => i.isEmbedding.injective (hw.trans hz.symm), fun hw => hw ▸ hz⟩
    exact he ▸ hxc.preimage i.continuous
  have hzη : z ≠ genericPoint Y := by
    intro he
    have hall : ∀ w : Y, w = z := by
      intro w
      apply Set.mem_singleton_iff.mp
      rw [← hzc.closure_eq]
      rw [he]
      exact ((genericPoint_spec Y).specializes trivial).mem_closure
    apply hFn
    intro y hy
    have hyr : y ∈ Set.range i := by rw [hr]; exact hy
    obtain ⟨w, hw⟩ := hyr
    exact Set.mem_singleton_iff.mpr (hw.symm.trans ((congrArg i (hall w)).trans hz))
  have : IsProper (i ≫ b) := inferInstance
  obtain ⟨C, j, hC, hdC, hj, hp, hzj⟩ :=
    exists_complete_integral_curve_through_closed_point Y k (i ≫ b) z hzc hzη
  have := hj
  obtain ⟨w, hw⟩ := hzj
  exact ⟨C, j ≫ i, hC, hdC, inferInstance,
    by simpa only [Category.assoc] using hp,
    ⟨w, by simpa only [Scheme.Hom.comp_apply, hw] using hz⟩⟩

end
end Negativity
