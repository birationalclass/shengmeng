module

public import Negativity.FiniteTypeProjectiveImmersion
public import Negativity.StandardProjectiveProper
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: from an actual quasi-compact integral scheme of finite
type over an actual affine base, construct the finite affine cover and
all its actual relative projective immersions used by Hartshorne's Chow
proof. The source cover, common nonempty open and projective dimensions
are constructed internally. No cover or immersion witness is supplied. -/
theorem exists_actual_hartshorne_affine_projective_cover
    {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens) (d : ι → ℕ)
      (j : ∀ i, (U i).toScheme ⟶ Proj
        (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) Γ(Y, ⊤)))
      (W : X.Opens),
      iSup U = ⊤ ∧ (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty (U i)) ∧ Nonempty W ∧ (∀ i, W ≤ U i) ∧
      (∀ i, IsImmersion (j i)) ∧
      (∀ i, j i ≫ actualProjectiveSpaceToSpec Γ(Y, ⊤) (d i) =
        (U i).ι ≫ f ≫ Y.toSpecΓ) ∧
      (∀ i, IsProper (actualProjectiveSpaceToSpec Γ(Y, ⊤) (d i))) := by
  classical
  obtain ⟨s, hs, hfin, hsup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (U := ⊤) (by simpa using isCompact_univ (X := X))
  let s' : Set X.Opens := {U | U ∈ s ∧ Nonempty U}
  have hfin' : s'.Finite := hfin.subset (fun _ h => h.1)
  let ι := s'
  letI : Fintype ι := hfin'.fintype
  let U : ι → X.Opens := fun i => i.1
  have hU : ∀ i, IsAffineOpen (U i) := fun i => hs i.2.1
  have hne : ∀ i, Nonempty (U i) := fun i => i.2.2
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x hx
    have hxs : x ∈ sSup s := by rw [← hsup]; trivial
    obtain ⟨V, hVs, hxV⟩ := Opens.mem_sSup.mp hxs
    exact Opens.mem_iSup.mpr ⟨⟨V, hVs, ⟨⟨x, hxV⟩⟩⟩, hxV⟩
  have hp (i : ι) : ∃ (n : ℕ) (g : (U i).toScheme ⟶ Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(Y, ⊤))),
      IsImmersion g ∧ g ≫ actualProjectiveSpaceToSpec Γ(Y, ⊤) n =
        (U i).ι ≫ f ≫ Y.toSpecΓ := by
    letI : IsAffine (U i).toScheme := hU i
    simpa only [Category.assoc] using
      exists_actual_affine_finite_type_projective_immersion ((U i).ι ≫ f)
  choose d j hj hb using hp
  let W : X.Opens := ⨅ i, U i
  have hW : Nonempty W := by
    refine ⟨⟨genericPoint X, ?_⟩⟩
    change genericPoint X ∈ (↑(⨅ i, U i) : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter]
    intro i
    obtain ⟨x, hx⟩ := hne i
    exact ((genericPoint_spec X).mem_open_set_iff (U i).isOpen).mpr ⟨x, trivial, hx⟩
  exact ⟨ι, inferInstance, U, d, j, W, hcover, hU, hne, hW,
    fun i => iInf_le U i, hj, hb, fun i => actual_standard_projective_space_proper _ _⟩

end
end Negativity
