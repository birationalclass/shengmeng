module

public import Negativity.AffineLineThroughPoint
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
set_option backward.isDefEq.respectTransparency false

/-- An integral domain integral over a ring of dimension at most one
also has dimension at most one. -/
theorem integral_extension_krullDimLE_one
    (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra B A] [Algebra.IsIntegral B A] [Ring.KrullDimLE 1 B] :
    Ring.KrullDimLE 1 A := by
  apply Ring.KrullDimLE.mk₁'
  intro P hP hp
  have := hp
  have hp0 : P.under B ≠ ⊥ := by
    intro h
    exact hP (Ideal.eq_bot_of_under_eq_bot h)
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under P
    (Ideal.isMaximal_of_isPrime_of_ne_bot _ hp0)

/-- Final theorem: every closed point of a positive-dimensional affine
integral variety over an algebraically closed field lies on an actual
integral affine curve. The curve is constructed as a prime quotient,
with dimension and positive dimension proved, not assumed. -/
theorem affine_integral_curve_through_maximal
    (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (hA : ¬ IsField A)
    (m : Ideal A) [m.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P < m ∧
      Ring.KrullDimLE 1 (A ⧸ P) ∧ ¬ IsField (A ⧸ P) := by
  classical
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral B A := ⟨hint⟩
  have hinj : Function.Injective (algebraMap B A) := hg
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    have hB : IsField B :=
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv.toMulEquiv.isField
        (Field.toIsField k)
    exact hA (isField_of_isIntegral_of_isField' hB)
  let q : Ideal B := m.under B
  have hq : q.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have := hq
  have : m.LiesOver q := ⟨rfl⟩
  obtain ⟨a, hqa⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hq
  obtain ⟨p, hp, hpq, ⟨e⟩⟩ := affine_line_kernel_below_point k n hn a
  have := hp
  have hpq' : p < q := by rwa [hqa]
  obtain ⟨P, hPm, hP, hPp⟩ := Ideal.exists_ideal_lt_liesOver_of_lt m hpq'
  have := hP
  have := hPp
  have : Algebra.IsIntegral (B ⧸ p) (A ⧸ P) := by
    have hpunder : p = P.under B := P.over_def p
    subst p
    infer_instance
  have hd : Ring.KrullDimLE 1 (B ⧸ p) := by
    rw [Ring.krullDimLE_iff, e.ringKrullDim, ← Ring.krullDimLE_iff]
    infer_instance
  have := hd
  have hdim : Ring.KrullDimLE 1 (A ⧸ P) :=
    integral_extension_krullDimLE_one (B ⧸ p) (A ⧸ P)
  have hnf : ¬ IsField (A ⧸ P) := by
    intro h
    have hb : IsField (B ⧸ p) := isField_of_isIntegral_of_isField
      (FaithfulSMul.algebraMap_injective (B ⧸ p) (A ⧸ P)) h
    exact Polynomial.not_isField k (e.symm.toMulEquiv.isField hb)
  exact ⟨P, hP, hPm, hdim, hnf⟩

end Negativity
