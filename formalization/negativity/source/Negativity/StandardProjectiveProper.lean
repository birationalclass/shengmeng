module

public import Negativity.RelativeProjectiveEmbedding
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_degree_zero_inclusion_bijective
    (R : Type u) [CommRing R] (n : ℕ) :
    Function.Bijective (projectiveDegreeZeroInclusion R n) := by
  constructor
  · intro r s h
    exact MvPolynomial.C_injective (Fin (n + 1)) R (congrArg Subtype.val h)
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hp)).symm

/-- Final theorem: the actual structure morphism of standard relative
projective space is proper over its actual base ring. Its degree-zero
subring is identified with the base by the genuine constant inclusion,
and the standard finite coordinate generators prove the Proj hypotheses. -/
theorem actual_standard_projective_space_proper
    (R : Type u) [CommRing R] (n : ℕ) :
    IsProper (actualProjectiveSpaceToSpec R n) := by
  classical
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  have : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) R) := by
    refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
    simpa using mvPolynomial_degree_zero_adjoin_variables R (Fin (n + 1))
  have : IsIso (CommRingCat.ofHom (projectiveDegreeZeroInclusion R n)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (projective_degree_zero_inclusion_bijective R n)
  unfold actualProjectiveSpaceToSpec
  infer_instance

end
end Negativity
