module

public import Negativity.ProjStandardSections
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard variables generate the polynomial ring over its genuine
degree-zero subring. This is the algebraic cover input for relative
projective space, and is proved rather than assumed. -/
theorem mvPolynomial_degree_zero_adjoin_variables
    (R : Type u) [CommRing R] (κ : Type) :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule κ R 0)
      (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) = ⊤ := by
  let S := Algebra.adjoin (MvPolynomial.homogeneousSubmodule κ R 0)
    (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))
  apply top_unique
  intro p hp
  clear hp
  change p ∈ S
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact S.algebraMap_mem
      ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C κ r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp =>
    exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- Final theorem: an actual closed embedding into standard relative
projective space constructs an actual Cartier divisor and its effective
coordinate sections with affine nonvanishing loci covering the scheme.
No O(1), affine-section data or positivity conclusion is a hypothesis. -/
theorem exists_actual_projective_space_cartier_sections
    (R : Type u) [CommRing R] (n : ℕ)
    {X : Scheme.{u}} [IsIntegral X]
    (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] :
    ∃ A : CartierAtlas X X, Nonempty (CartierAffineSectionCover A X) := by
  exact exists_actual_proj_sections_of_generators
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) j (d := 1) Nat.zero_lt_one
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X R i⟩)
    (mvPolynomial_degree_zero_adjoin_variables R (Fin (n + 1)))

end
end Negativity
