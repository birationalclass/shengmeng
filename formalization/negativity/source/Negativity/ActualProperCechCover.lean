module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: an actual proper scheme over an actual affine base
has an internally constructed finite affine Cech cover whose pairwise
and triple intersections are affine. Neither a finite cover nor its
intersection affineness is supplied as a geometric input. -/
theorem exists_actual_proper_affine_cech_cover
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.affineOpens),
      iSup (fun k => (U k).1) = ⊤ ∧
        (∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) ∧
        (∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨s, hs, hfin, hsup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (U := ⊤) (by simpa using isCompact_univ (X := X))
  let ι := s
  letI : Fintype ι := hfin.fintype
  let U : ι → X.affineOpens := fun k => ⟨k.1, hs k.2⟩
  have hcover : iSup (fun k => (U k).1) = ⊤ := by
    apply top_unique
    intro x hx
    have hxs : x ∈ sSup s := by rw [← hsup]; trivial
    obtain ⟨V, hVs, hxV⟩ := Opens.mem_sSup.mp hxs
    exact Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hxV⟩
  exact ⟨ι, inferInstance, U, hcover, fun j k => (U j).2.inf (U k).2,
    fun j k l => ((U j).2.inf (U k).2).inf (U l).2⟩

end
end Negativity
