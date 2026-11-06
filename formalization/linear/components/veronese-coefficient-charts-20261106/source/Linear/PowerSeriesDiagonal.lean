module
public import Linear.NilpotentEvaluationUnique
public import Linear.PolynomialDiagonal
public import Linear.DeterminantAnnihilator

/-!
# Power-series difference matrices and actual diagonal Jacobians

Nilpotent variable images permit finite polynomial truncation retaining
both values and partial derivatives. Construct a difference matrix whose
determinant annihilates variable differences, and whose diagonal image is
the actual derivative Jacobian. Nonvanishing and the trace comparison
are separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {R A B ι : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem powerSeries_diagonal_difference
    (u v : MvPowerSeries ι R →+* A) (π : A →+* B)
    (hC : ∀ c, u (MvPowerSeries.C c) = v (MvPowerSeries.C c))
    (hX : ∀ i, π (u (MvPowerSeries.X i)) = π (v (MvPowerSeries.X i)))
    (hu : ∀ i, IsNilpotent (u (MvPowerSeries.X i)))
    (hv : ∀ i, IsNilpotent (v (MvPowerSeries.X i)))
    (H : MvPowerSeries ι R) :
    ∃ a : ι → A,
      u H - v H = ∑ i, a i * (u (MvPowerSeries.X i) - v (MvPowerSeries.X i)) ∧
      ∀ i, π (a i) = π (u (MvPowerSeries.pderiv i H)) := by
  classical
  choose bu hbu using hu
  choose bv hbv using hv
  let b : ι → ℕ := fun i => max (bu i) (bv i)
  have hbu' : ∀ i, u (MvPowerSeries.X i) ^ b i = 0 := by
    intro i; exact pow_eq_zero_of_le (Nat.le_max_left _ _) (hbu i)
  have hbv' : ∀ i, v (MvPowerSeries.X i) ^ b i = 0 := by
    intro i; exact pow_eq_zero_of_le (Nat.le_max_right _ _) (hbv i)
  let p := MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm (fun i => b i + 1)) H
  have hup : u H = u (p : MvPowerSeries ι R) :=
    powerSeries_map_eq_trunc_of_nilpotent u (fun i => b i + 1)
      (fun i => pow_eq_zero_of_le (Nat.le_succ _) (hbu' i)) H
  have hvp : v H = v (p : MvPowerSeries ι R) :=
    powerSeries_map_eq_trunc_of_nilpotent v (fun i => b i + 1)
      (fun i => pow_eq_zero_of_le (Nat.le_succ _) (hbv' i)) H
  let up := u.comp MvPolynomial.coeToMvPowerSeries.ringHom
  let vp := v.comp MvPolynomial.coeToMvPowerSeries.ringHom
  obtain ⟨a, ha, hda⟩ := polynomial_diagonal_difference up vp π
    (by intro c; simpa [up, vp] using hC c)
    (by intro i; simpa [up, vp] using hX i) p
  refine ⟨a, ?_, ?_⟩
  · rw [hup, hvp]
    simpa [up, vp] using ha
  · intro i
    rw [hda i]
    exact (powerSeries_map_pderiv_eq_trunc_of_nilpotent (π.comp u) b
      (by intro j; simp only [RingHom.comp_apply, ← map_pow, hbu', map_zero]) H i).symm

theorem powerSeries_diagonal_jacobian_matrix
    (u v : MvPowerSeries ι R →+* A) (π : A →+* B)
    (hC : ∀ c, u (MvPowerSeries.C c) = v (MvPowerSeries.C c))
    (hX : ∀ i, π (u (MvPowerSeries.X i)) = π (v (MvPowerSeries.X i)))
    (hu : ∀ i, IsNilpotent (u (MvPowerSeries.X i)))
    (hv : ∀ i, IsNilpotent (v (MvPowerSeries.X i)))
    (H : ι → MvPowerSeries ι R) (hH : ∀ i, u (H i) = v (H i)) :
    ∃ M : Matrix ι ι A,
      Annihilates (Ideal.span (Set.range (fun i =>
        u (MvPowerSeries.X i) - v (MvPowerSeries.X i)))) M.det ∧
      M.map π = (fun i j => π (u (MvPowerSeries.pderiv j (H i)))) ∧
      π M.det = Matrix.det (fun i j => π (u (MvPowerSeries.pderiv j (H i)))) := by
  classical
  have hd := fun i => powerSeries_diagonal_difference u v π hC hX hu hv (H i)
  choose M hM hdM using hd
  let N : Matrix ι ι A := fun i j => M i j
  have hrel : N.mulVec
      (fun i => u (MvPowerSeries.X i) - v (MvPowerSeries.X i)) = 0 := by
    funext i
    change (∑ j, M i j * (u (MvPowerSeries.X j) - v (MvPowerSeries.X j))) = 0
    rw [← hM i, hH i, sub_self]
  have heq : N.map π =
      (fun i j => π (u (MvPowerSeries.pderiv j (H i)))) := by
    funext i j; exact hdM i j
  refine ⟨N, determinant_annihilates_coordinate_ideal N _ hrel, heq, ?_⟩
  rw [π.map_det]
  change Matrix.det (N.map π) = _
  rw [heq]

end LinearStudy
