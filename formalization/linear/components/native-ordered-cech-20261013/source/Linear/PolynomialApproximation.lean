module
public import Linear.NilpotentEvaluationUnique
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# PolynomialApproximation

Finite polynomial truncations of nilpotent power-series equations are obtained by a matrix whose constant-coefficient matrix is the identity. Its determinant and the matrix are units. No regularity or Jacobian nonvanishing is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace LinearStudy
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem powerSeries_polynomial_equations_unit_change
    (H : ι → MvPowerSeries ι R) (b : ι → ℕ)
    (hb : ∀ i, (MvPowerSeries.X i : MvPowerSeries ι R) ^ b i ∈
      Ideal.span (Set.range H)) :
    ∃ P : ι → MvPolynomial ι R,
      (∀ i, P i = MvPowerSeries.trunc' R
        (Finsupp.equivFunOnFinite.symm (fun j => b j + 1)) (H i)) ∧
      ∃ U : Matrix ι ι (MvPowerSeries ι R),
        IsUnit U ∧ U.mulVec H = (fun i => (P i : MvPowerSeries ι R)) ∧
        U.map MvPowerSeries.constantCoeff = 1 := by
  classical
  let bound : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => b i + 1)
  let P : ι → MvPolynomial ι R := fun i => MvPowerSeries.trunc' R bound (H i)
  have hz : ∀ i, ∀ m : ι →₀ ℕ, (∀ j, m j < b j + 1) →
      (H i - (P i : MvPowerSeries ι R)).coeff m = 0 := by
    intro i m hm
    have hle : m ≤ bound := fun j => Nat.le_of_lt (hm j)
    simp [P, map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', hle]
  choose A hA using fun i => powerSeries_boxZero_expansion
    (H i - (P i : MvPowerSeries ι R)) (fun j => b j + 1) (hz i)
  choose B hB using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hb i)
  let Am : Matrix ι ι (MvPowerSeries ι R) := A
  let Bm : Matrix ι ι (MvPowerSeries ι R) := B
  let Xd : Matrix ι ι (MvPowerSeries ι R) := Matrix.diagonal MvPowerSeries.X
  let K : Matrix ι ι (MvPowerSeries ι R) := Am * Xd * Bm
  have hBv : Bm.mulVec H = fun i => MvPowerSeries.X i ^ b i := by
    funext i
    exact hB i
  have hKv : K.mulVec H = fun i => H i - (P i : MvPowerSeries ι R) := by
    rw [show K = Am * Xd * Bm from rfl, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hBv]
    change Am.mulVec ((Matrix.diagonal MvPowerSeries.X).mulVec
      (fun i => MvPowerSeries.X i ^ b i)) = _
    have hdv : (Matrix.diagonal (MvPowerSeries.X (σ := ι) (R := R))).mulVec
        (fun i => MvPowerSeries.X i ^ b i) =
        (fun i => MvPowerSeries.X i * MvPowerSeries.X i ^ b i) := by
      funext i
      exact Matrix.mulVec_diagonal _ _ i
    rw [hdv]
    funext i
    change (∑ j, A i j * (MvPowerSeries.X j * MvPowerSeries.X j ^ b j)) = _
    simp_rw [← pow_succ']
    exact (hA i).symm
  let U : Matrix ι ι (MvPowerSeries ι R) := 1 - K
  have hUv : U.mulVec H = fun i => (P i : MvPowerSeries ι R) := by
    rw [show U = 1 - K from rfl, Matrix.sub_mulVec, Matrix.one_mulVec, hKv]
    funext i
    simp
  have hXmap : Xd.map MvPowerSeries.constantCoeff = 0 := by
    ext i j
    by_cases h : i = j <;> simp [Xd, Matrix.diagonal, Matrix.map_apply, h]
  have hUmap : U.map MvPowerSeries.constantCoeff = 1 := by
    change (MvPowerSeries.constantCoeff (σ := ι) (R := R)).mapMatrix U = 1
    simp only [U, K, map_sub, map_one, map_mul]
    change 1 - Am.map MvPowerSeries.constantCoeff *
      Xd.map MvPowerSeries.constantCoeff * Bm.map MvPowerSeries.constantCoeff = 1
    simp [hXmap]
  have hdet : IsUnit U.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    rw [(MvPowerSeries.constantCoeff (σ := ι) (R := R)).map_det]
    change IsUnit (U.map MvPowerSeries.constantCoeff).det
    rw [hUmap, Matrix.det_one]
    exact isUnit_one
  exact ⟨P, fun _ => rfl, U, (Matrix.isUnit_iff_isUnit_det U).mpr hdet, hUv, hUmap⟩

end LinearStudy
