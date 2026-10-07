module
public import Linear.LocalizedAnnihilator
public import Linear.PointDecomposition
public import Mathlib.Tactic
/-! Actual affine Euler-Jacobi weighted point relation, conditional on regular highest parts, origin-only highest zero locus and local socle generation by the chosen polynomial. All point weights are constructed and proved nonzero. Geometric charts supplying the local hypotheses remain unproved. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
attribute [local instance] Fintype.ofFinite
variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

theorem affine_polynomial_weighted_point_relation {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (he : ∀ i, 0 < (P i).totalDegree)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0})
    (Theta : MvPolynomial (Fin (n + 1)) K)
    (hloc : let Q := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P)
      let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
      ∀ (J : Ideal Q) [J.IsMaximal],
        (nilradical (Localization.AtPrime J)).annihilator =
          Ideal.span {algebraMap Q (Localization.AtPrime J) (pi Theta)}) :
    let Q := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P)
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    letI : Module.Finite K Q := polynomialQuotient_finite_of_top_zeroLocus P hz
    letI : IsArtinianRing Q := IsArtinianRing.of_finite K Q
    ∃ q : MaximalSpectrum Q → Q →ₐ[K] K,
      (∀ j, RingHom.ker (q j).toRingHom = j.asIdeal) ∧
      ∃ lam : MaximalSpectrum Q → K, (∀ j, lam j ≠ 0) ∧
        ∀ f : MvPolynomial (Fin (n + 1)) K,
          Theta.totalDegree + f.totalDegree < ∑ i, ((P i).totalDegree - 1) →
            ∑ j : MaximalSpectrum Q, lam j * q j (pi f) = 0 := by
  classical
  let Q := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P)
  let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
  let : Module.Finite K Q := polynomialQuotient_finite_of_top_zeroLocus P hz
  let : IsArtinianRing Q := IsArtinianRing.of_finite K Q
  let : IsNoetherianRing Q := IsNoetherianRing.of_finite K Q
  choose q hq using fun j : MaximalSpectrum Q => exists_maximalResidueMap (K := K) j
  have hgen : (nilradical Q).annihilator = Ideal.span {pi Theta} :=
    nilradical_annihilator_generator_of_localizations (pi Theta) hloc
  obtain ⟨p, hv, _⟩ := affine_polynomial_low_degree_trace_pairing P he hreg hz
  obtain ⟨lam, hlam, hsum⟩ := perfect_nilradical_socle_weighted_evaluation q hq p (pi Theta) hgen
  refine ⟨q, hq, lam, hlam, ?_⟩
  intro f hf
  have hdegree : (f * Theta).totalDegree < ∑ i, ((P i).totalDegree - 1) :=
    (MvPolynomial.totalDegree_mul f Theta).trans_lt (by simpa only [add_comm] using hf)
  have hzero : p.functional (pi (f * Theta)) = 0 := hv (f * Theta) hdegree
  rw [map_mul, hsum] at hzero
  exact hzero

end LinearStudy
