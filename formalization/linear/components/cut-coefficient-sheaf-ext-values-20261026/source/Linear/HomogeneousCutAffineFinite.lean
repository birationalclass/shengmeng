module
public import Linear.HomogeneousConeAffineFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- No original cut point at infinity DERIVES finiteness of the ACTUAL
affine map defined by those SAME dehomogenized cut equations. Use the
actual cone tuple [X0^q,H1,...,Hr],not a generic finite-map certificate.
The resulting coefficient dual is NOT identified with the fixed original
normalization dual;that comparison and SAME top-H calibration remain OPEN. -/
theorem homogeneous_cut_no_infinity_actual_affine_map_finite
    {K : Type*} [Field K] [IsAlgClosed K] {n r q : ℕ}
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K))
    (v : Fin (n+1) → K) (hv : v ∈ MvPolynomial.zeroLocus K I)
    (H : Fin r → MvPolynomial (Fin (n+1)) K)
    (hq : 0 < q) (hH : ∀ i,(H i).IsHomogeneous q)
    (hno : ∀ z : Fin (n+1) → K,z ≠ 0 → z ∈ MvPolynomial.zeroLocus K I →
      z 0=0 → ∃ i,MvPolynomial.eval z (H i) ≠ 0) :
    (((Ideal.Quotient.mkₐ K (I.map (affineChartPolynomialMap (K:=K)).toRingHom)).comp
      (MvPolynomial.aeval (fun i : Fin r => affineChartPolynomialMap (K:=K) (H i))) :
      MvPolynomial (Fin r) K →ₐ[K]
        MvPolynomial (Fin n) K ⧸ I.map (affineChartPolynomialMap (K:=K)).toRingHom).toRingHom).Finite := by
  let P : Fin (r+1) → MvPolynomial (Fin (n+1)) K :=
    Fin.cases ((MvPolynomial.X 0)^q) H
  have hP (i : Fin (r+1)) : (P i).IsHomogeneous q := by
    cases i using Fin.cases with
    | zero => exact MvPolynomial.isHomogeneous_X_pow 0 q
    | succ i => exact hH i
  have hbase : ∀ z : Fin (n+1) → K,z ≠ 0 → z ∈ MvPolynomial.zeroLocus K I →
      ∃ i,MvPolynomial.eval z (P i) ≠ 0 := by
    intro z hz hIz
    by_cases hz0 : z 0=0
    · obtain ⟨i,hi⟩ := hno z hz hIz hz0
      exact ⟨i.succ,hi⟩
    · refine ⟨0,?_⟩
      change MvPolynomial.eval z ((MvPolynomial.X 0)^q) ≠ 0
      simpa only [map_pow,MvPolynomial.eval_X] using pow_ne_zero q hz0
  have hfin := homogeneous_quotient_map_finite_of_no_base_points I hI v hv P q hq hP hbase
  have hfirst : affineChartPolynomialMap (K:=K) (P 0)=1 := by
    simp [P,affineChartPolynomialMap]
  exact homogeneous_cone_finite_implies_actual_affine_map_finite I P hfin hfirst
end LinearStudy
