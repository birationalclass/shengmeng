module

public import Negativity.HartshorneFiniteModification
public import Negativity.BirationalComposition
public import Negativity.GenericNormalizationBirational
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: Hartshorne's finite-product graph construction and
actual finite normalization produce an actual normal integral proper
birational surjective modification, finite over the actual projective
product target. This works over any algebraically closed field in every
characteristic. No modification, normalization finiteness, birational
composition, normal-stalk or projection-finiteness witness is supplied.
Product Cartier section geometry is still needed for the proper
negativity theorem, so no complete main-target claim is made here. -/
theorem exists_actual_normal_hartshorne_modification
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (P N : Scheme.{u})
      (p : P ⟶ Spec (.of Γ(Y, ⊤)))
      (a : ∀ i, P ⟶ Proj
        (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) Γ(Y, ⊤)))
      (π : N ⟶ X) (q : N ⟶ P),
      IsProper p ∧ (∀ i, a i ≫ actualProjectiveSpaceToSpec Γ(Y, ⊤) (d i) = p) ∧
      (∀ (V : ∀ i, (Proj
        (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) Γ(Y, ⊤))).Opens),
        (∀ i, IsAffineOpen (V i)) → IsAffineOpen (⨅ i, a i ⁻¹ᵁ V i)) ∧
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z)) ∧
      IsProper π ∧ BirationalMorphism π ∧ Surjective π ∧
      IsFinite q ∧ π ≫ f ≫ Y.toSpecΓ = q ≫ p := by
  obtain ⟨n, d, P, Z, p, a, π, q, hp, ha, haff, hint, hπ, hbir, hsur, hq, hw⟩ :=
    exists_actual_hartshorne_finite_modification f
  have : IsIntegral Z := hint
  have : IsProper π := hπ
  have : IsFinite q := hq
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian π
  let g := Z.fromSpecStalk (genericPoint Z)
  let ν := g.fromNormalization
  have : IsFinite ν := finiteType_perfectField_normalization_isFinite Z k (π ≫ f ≫ b)
  have hν : BirationalMorphism ν :=
    finiteType_perfectField_normalization_birational Z k (π ≫ f ≫ b)
  have : IsLocallyNoetherian g.normalization := LocallyOfFiniteType.isLocallyNoetherian ν
  have hcomp : BirationalMorphism (ν ≫ π) := actual_birational_morphism_comp ν π hν hbir
  refine ⟨n, d, P, g.normalization, p, a, ν ≫ π, ν ≫ q,
    hp, ha, haff, inferInstance, inferInstance, generic_normalization_stalks_normal Z,
    inferInstance, hcomp, proper_birational_surjective (ν ≫ π) hcomp,
    inferInstance, ?_⟩
  simp only [Category.assoc]
  rw [hw]

end
end Negativity
