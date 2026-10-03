module

public import Negativity.AffineCurveThroughPoint
public import Negativity.AffineLineAvoiding
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
set_option backward.isDefEq.respectTransparency false

/-- Final theorem: construct an actual integral affine curve through
a prescribed closed point on a nonzero function's zero set, while
avoiding containment in that zero set. No support-avoidance or curve
existence input is assumed. -/
theorem affine_integral_curve_through_maximal_avoiding
    (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (hA : ¬ IsField A)
    (m : Ideal A) [m.IsMaximal] (v : A) (hv : v ≠ 0) (hvm : v ∈ m) :
    ∃ P : Ideal A, P.IsPrime ∧ P < m ∧ v ∉ P ∧
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
  let J : Ideal A := Ideal.span {v}
  have hJm : J ≤ m := (Ideal.span_singleton_le_iff_mem m).mpr hvm
  have hJ : J.under B ≠ ⊥ := Ideal.under_ne_bot_of_integral_mem hv
    (Ideal.mem_span_singleton_self v) (Algebra.IsIntegral.isIntegral v)
  obtain ⟨w, hw, hw0⟩ := (J.under B).ne_bot_iff.mp hJ
  have hwq : w ∈ q := hJm hw
  have hwa : MvPolynomial.eval a w = 0 := by
    have hwqa : w ∈ MvPolynomial.vanishingIdeal k {a} := hqa ▸ hwq
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff a w).mp hwqa
  obtain ⟨p, hp, hpq, hwp, ⟨e⟩⟩ :=
    affine_line_through_point_avoiding_polynomial k n a w hw0 hwa
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
  have hvP : v ∉ P := by
    intro hvP
    have hJP : J ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hvP
    have hwP : algebraMap B A w ∈ P := hJP hw
    have hwu : w ∈ P.under B := hwP
    have hwe : w ∈ p := (P.over_def p).symm ▸ hwu
    exact hwp hwe
  exact ⟨P, hP, hPm, hvP, hdim, hnf⟩

end Negativity
