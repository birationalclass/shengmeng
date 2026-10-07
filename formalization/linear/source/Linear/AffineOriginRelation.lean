module
public import Linear.OriginRegular
public import Linear.AffinePointRelation
public import Linear.ProjectiveChart
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] [IsAlgClosed K]
attribute [local instance] Fintype.ofFinite

theorem polynomial_highest_parts_regular_of_zeroLocus {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) K)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0}) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))) :=
  homogeneous_origin_regular n _ (fun i =>
    ⟨(P i).totalDegree, MvPolynomial.homogeneousComponent_isHomogeneous _ _⟩) hz

theorem affine_origin_low_degree_trace_pairing [CharZero K] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (he : ∀ i, 0 < (P i).totalDegree)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0}) :
    let I := Ideal.span (Set.range P)
    let Q := MvPolynomial (Fin (n + 1)) K ⧸ I
    let pi := Ideal.Quotient.mk I
    ∃ p : PerfectMultiplicationPairing (B := K) (A := Q),
      (∀ f : MvPolynomial (Fin (n + 1)) K,
        f.totalDegree < ∑ i, ((P i).totalDegree - 1) → p.functional (pi f) = 0) ∧
      ∀ a : Q, p.functional (a * Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i)))) =
        Algebra.trace K Q a :=
  affine_polynomial_low_degree_trace_pairing P he
    (polynomial_highest_parts_regular_of_zeroLocus P hz) hz

theorem affine_origin_weighted_point_relation [CharZero K] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (he : ∀ i, 0 < (P i).totalDegree)
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
            ∑ j : MaximalSpectrum Q, lam j * q j (pi f) = 0 :=
  affine_polynomial_weighted_point_relation P he
    (polynomial_highest_parts_regular_of_zeroLocus P hz) hz Theta hloc

theorem projectiveFiber_actual_highest_regular {n : ℕ} (f : HomogeneousEndomorphism n)
    (hq : 0 < f.degree)
    (hn : ∀ i : Fin n, (MvPolynomial.finSuccEquiv ℂ n (f.forms i.succ)).coeff 0 ≠ 0)
    (havoid : ∀ v : CoordinateVector n, ∀ hv : v ≠ 0, v 0 = 0 →
      f.onPoints (Projectivization.mk ℂ v hv) ≠ standardProjectivePoint n) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) ℂ)
      (List.ofFn (fun i : Fin n =>
        MvPolynomial.homogeneousComponent (affineDehomogenize (f.forms i.succ)).totalDegree
          (affineDehomogenize (f.forms i.succ)))) :=
  polynomial_highest_parts_regular_of_zeroLocus _
    (projectiveFiber_actual_highest_zeroLocus f hq hn havoid)
end LinearStudy
