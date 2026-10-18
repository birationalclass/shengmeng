module
public import Linear.IntegralKrullDimension
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Noether normalization with its actual number of variables proved
equal to the actual Krull dimension, rather than supplied as a parameter. -/
theorem exists_finite_normalization_krull_dimension
    (k A : Type*) [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] A,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim A = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  letI : Module.Finite (MvPolynomial (Fin s) k) A :=
    RingHom.finite_algebraMap.mp hfinite
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := inferInstance
  have hdim := integral_injective_ringKrullDim_eq (MvPolynomial (Fin s) k) A hinj
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, Nat.card_fin, zero_add] at hdim
  exact ⟨s, g, hinj, hfinite, hdim.symm⟩

end LinearStudy
