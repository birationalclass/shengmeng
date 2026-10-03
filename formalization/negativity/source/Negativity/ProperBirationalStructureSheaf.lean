module

public import Negativity.ProperBirationalFunctions
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The actual structure-sheaf pullback O_Y → f_*O_X, as a morphism of
genuine sheaves on the actual base topological space. -/
def actualStructureSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf :=
  ⟨f.c⟩

/-- Final theorem: the actual natural structure-sheaf map of a proper
birational morphism to a normal locally Noetherian integral base is an
isomorphism. Affine descent is proved by actual codimension-one extension,
and the genuine sheaf basis theorem glues its actual inverses. No H^0
finiteness, Stein factorization, direct-image equality or connectedness
input is assumed. Fiber connectedness remains a subsequent geometric
theorem, not a consequence asserted merely from this declaration. -/
theorem proper_normal_birational_structure_sheaf_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsIso (actualStructureSheafPullback f) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : Y.affineOpens => U.1)
    (by simpa using Y.isBasis_affineOpens)
  intro U
  change IsIso (f.app U.1)
  by_cases hne : Nonempty U.1
  · have : Nonempty U.1 := hne
    have : Nonempty (f ⁻¹ᵁ U.1) := by
      obtain ⟨y, hy⟩ := hne
      obtain ⟨x, hx⟩ := (proper_birational_surjective f hf).surj y
      exact ⟨⟨x, by change f x ∈ U.1; rwa [hx]⟩⟩
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (proper_normal_birational_affine_functions_bijective f hf hnY U.1 U.2)
  · have hz : U.1 = ⊥ := by
      ext x
      change x ∈ U.1 ↔ False
      exact ⟨fun hx => hne ⟨⟨x, hx⟩⟩, False.elim⟩
    rw [hz]
    exact isIso_of_isTerminal Y.sheaf.isTerminalOfEmpty
      (X.sheaf.isTerminalOfEqEmpty (by simp)) (f.app ⊥)

end
end Negativity
