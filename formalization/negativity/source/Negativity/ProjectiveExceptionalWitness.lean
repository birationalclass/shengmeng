module

public import Negativity.EffectiveExceptionalWitness
public import Negativity.ProjPolynomialSections
public import Negativity.CartierInverse
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: construct the actual effective exceptional Cartier E
from the actual relative projective embedding over an affine normal
birational base. E has strictly positive coefficients at all exceptional
primes and strictly negative actual normalized degree on every closed
contracted complete integral curve. Every one of these properties is an
output; no Cartier, section, effectivity, coverage or degree-sign input
is assumed. -/
theorem exists_actual_projective_exceptional_cartier
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (n : ℕ)
    (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(Y, ⊤)))
    [IsClosedImmersion j] :
    ∃ E : CartierAtlas X X, E.Effective ∧
      (∀ x : X, Order.coheight x = 1 →
        (∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U)) → 0 < E.coefficient hnX x) ∧
      (∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
        (i : C ⟶ X) [IsProper (i ≫ f ≫ b)], IsClosedImmersion i →
        (∀ c : C, f (i c) = f (i (genericPoint C))) →
        normalizedCartierCurveIntersection hd k (i ≫ f ≫ b) i E < 0) := by
  obtain ⟨A, ⟨S⟩⟩ := exists_actual_projective_space_cartier_sections Γ(Y, ⊤) n j
  have hanti : ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
      (i : C ⟶ X) [IsProper (i ≫ f ≫ b)], IsClosedImmersion i →
      (∀ c : C, f (i c) = f (i (genericPoint C))) →
      normalizedCartierCurveIntersection hd k (i ≫ f ≫ b) i A.inverse < 0 := by
    intro C _ hd i _ hi _hc
    have := hi
    rw [complete_integral_curve_cartier_intersection_inverse hnX hd k (i ≫ f ≫ b) i A]
    exact neg_neg_of_pos (complete_integral_curve_positive_of_affine_section_cover
      hd k (i ≫ f ≫ b) i A S)
  obtain ⟨s, hE, hcover⟩ := exists_effective_exceptional_covering_cartier_twist
    k b f hf hnX hnY A.inverse hanti
  refine ⟨A.inverse.rationalTwist s, hE, hcover, ?_⟩
  intro C _ hd i _ hi hc
  rw [complete_integral_curve_ambient_cartier_principal_invariance
    hd k (i ≫ f ≫ b) i A.inverse s]
  exact hanti C hd i hi hc

end
end Negativity
