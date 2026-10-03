module

public import Negativity.ProjCartierSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: homogeneous generators of one positive degree construct
actual Cartier affine-section geometry on a closed integral subscheme of
Proj. The pointwise coordinate choices and all Cartier section data are
outputs, rather than additional assumptions. -/
theorem exists_actual_proj_sections_of_generators
    {R : Type u} {σ : Type*} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} [IsIntegral X]
    (j : X ⟶ Proj 𝒜) [IsClosedImmersion j] {d : ℕ} (hd : 0 < d)
    {κ : Type*} (v : κ → 𝒜 d)
    (hv : Algebra.adjoin (𝒜 0) (Set.range (fun i => (v i : R))) = ⊤) :
    ∃ A : CartierAtlas X X, Nonempty (CartierAffineSectionCover A X) := by
  classical
  have htop := Proj.iSup_basicOpen_eq_top' 𝒜 (fun i => (v i : R))
    (fun i => ⟨d, (v i).2⟩) hv
  have hcover : ∀ x : X, ∃ i, j x ∈ Proj.basicOpen 𝒜 (v i : R) := by
    intro x
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [htop]
    trivial
  choose idx hidx using hcover
  exact exists_actual_proj_cartier_affine_section_cover 𝒜 j hd
    (fun x => v (idx x)) hidx

end
end Negativity
