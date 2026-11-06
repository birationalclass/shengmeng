module
public import Linear.Projective
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Analysis.Complex.Polynomial.Basic
/-! Actual projective total invariance implies a radical equality for the
homogeneous polynomial pullback ideal, and a positive-power sandwich that
transports along every actual ring map. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomial_pullback_zeroLocus
    {K σ : Type*} [Field K]
    (P : σ → MvPolynomial σ K) (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial.zeroLocus K (I.map (MvPolynomial.aeval P).toRingHom) =
      (fun v i => MvPolynomial.eval v (P i)) ⁻¹' MvPolynomial.zeroLocus K I := by
  ext v
  constructor
  · intro hv H hH
    have h := hv ((MvPolynomial.aeval P) H) (Ideal.mem_map_of_mem _ hH)
    change MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C P H) = 0 at h
    exact (MvPolynomial.eval_assoc P v H).trans h
  · intro hv
    change I.map (MvPolynomial.aeval P).toRingHom ≤
      RingHom.ker (MvPolynomial.aeval v).toRingHom
    apply Ideal.map_le_iff_le_comap.mpr
    intro H hH
    change MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C P H) = 0
    rw [← MvPolynomial.eval_assoc]
    exact hv H hH

theorem IntegralProjectiveEquations.origin_vanishes {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    0 ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := by
  obtain ⟨v, hv, hV⟩ := V.nonempty
  have h := homogeneous_ideal_vanish_smul V.ideal v hV 0
  change ∀ P ∈ V.ideal.toIdeal, MvPolynomial.eval 0 P = 0
  simpa only [zero_smul] using h

theorem HomogeneousEndomorphism.evalVector_zero {n : ℕ}
    (f : HomogeneousEndomorphism n) (hf : f.degree ≠ 0) : f.evalVector 0 = 0 := by
  have h := f.evalVector_smul 0 (0 : CoordinateVector n)
  simpa only [zero_smul, zero_pow hf] using h

theorem projective_total_invariance_cone
    {n : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    f.evalVector ⁻¹' MvPolynomial.zeroLocus ℂ V.ideal.toIdeal =
      MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := by
  ext v
  by_cases hv : v = 0
  · subst v
    change f.evalVector 0 ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal ↔
      0 ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal
    rw [f.evalVector_zero hf]
  · have h : f.onPoints (Projectivization.mk ℂ v hv) ∈ V.zeroSet ↔
        Projectivization.mk ℂ v hv ∈ V.zeroSet := by
      change Projectivization.mk ℂ v hv ∈ f.onPoints ⁻¹' V.zeroSet ↔ _
      rw [hV]
    rw [f.onPoints_mk, V.mem_zeroSet_mk, V.mem_zeroSet_mk] at h
    exact h

theorem projective_total_invariance_pullback_radical
    {n : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).radical =
      V.ideal.toIdeal := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    polynomial_pullback_zeroLocus]
  change MvPolynomial.vanishingIdeal ℂ
    (f.evalVector ⁻¹' MvPolynomial.zeroLocus ℂ V.ideal.toIdeal) = _
  rw [projective_total_invariance_cone f V hf hV,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
  exact V.prime.radical

theorem projective_total_invariance_ideal_power_sandwich
    {n : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    ∃ e : ℕ, 0 < e ∧
      V.ideal.toIdeal ^ e ≤ V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom ∧
      V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom ≤ V.ideal.toIdeal := by
  let J := V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom
  have hrad : J.radical = V.ideal.toIdeal :=
    projective_total_invariance_pullback_radical f V hf hV
  obtain ⟨e, he⟩ := J.exists_radical_pow_le_of_fg (IsNoetherian.noetherian _)
  refine ⟨e + 1, Nat.zero_lt_succ _, ?_, ?_⟩
  · have h : J.radical ^ (e + 1) ≤ J :=
      (Ideal.pow_le_pow_right (Nat.le_succ e)).trans he
    rwa [hrad] at h
  · have h : J ≤ J.radical := Ideal.le_radical
    rwa [hrad] at h

theorem projective_total_invariance_formal_sandwich
    {n : ℕ} (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    {S : Type*} [CommRing S] (ψ : CoordinateRing n →+* S) :
    ∃ e : ℕ, 0 < e ∧
      (V.ideal.toIdeal.map ψ) ^ e ≤
        (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map ψ ∧
      (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map ψ ≤
        V.ideal.toIdeal.map ψ := by
  obtain ⟨e, he, hlower, hupper⟩ := projective_total_invariance_ideal_power_sandwich f V hf hV
  refine ⟨e, he, ?_, Ideal.map_mono hupper⟩
  have h := Ideal.map_mono (f := ψ) hlower
  rwa [Ideal.map_pow] at h

end LinearStudy
