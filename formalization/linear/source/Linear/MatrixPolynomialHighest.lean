module
public import Linear.PolynomialCoordinateOrigin
public import Linear.ProjectiveCenteredFiberIdeal
public import Linear.PolynomialLinearHighestComponents
public import Linear.ProjectiveFiberHighestRegular
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace LinearStudy

theorem homogeneousComponent_matrix_polynomial_combination
    {K σ τ : Type*} [CommRing K] [Fintype τ]
    (M : Matrix τ τ K) (P : τ → MvPolynomial σ K) (q : ℕ) (i : τ) :
    MvPolynomial.homogeneousComponent q (MvPolynomial.aeval P (M.toMvPolynomial i)) =
      MvPolynomial.aeval (fun j => MvPolynomial.homogeneousComponent q (P j)) (M.toMvPolynomial i) := by
  classical
  simp only [Matrix.toMvPolynomial, ← MvPolynomial.C_mul_X_eq_monomial, map_sum,
    map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    MvPolynomial.algebraMap_eq, MvPolynomial.homogeneousComponent_C_mul]

theorem matrix_polynomial_combination_totalDegree_le
    {K σ τ : Type*} [CommRing K] [Fintype τ]
    (M : Matrix τ τ K) (P : τ → MvPolynomial σ K) (q : ℕ)
    (hP : ∀ j, (P j).totalDegree ≤ q) (i : τ) :
    (MvPolynomial.aeval P (M.toMvPolynomial i)).totalDegree ≤ q := by
  classical
  simp only [Matrix.toMvPolynomial, ← MvPolynomial.C_mul_X_eq_monomial, map_sum,
    map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hP j)

/-- Actual source coordinates and invertible target combinations preserve
the origin-only zero locus of the SAME degree-q highest components. -/
theorem polynomial_equation_coordinates_highest_zeroLocus
    {K σ τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (M : Matrix τ τ K) (hM : Matrix.det M ≠ 0)
    (P : σ → MvPolynomial σ K) (q : ℕ)
    (hE : ∀ G, MvPolynomial.homogeneousComponent q (E G) =
      E (MvPolynomial.homogeneousComponent q G))
    (h0 : ∀ j, MvPolynomial.eval (0 : σ → K) (E.symm (MvPolynomial.X j)) = 0)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (P i)))) = {0}) :
    let Pc := fun i => MvPolynomial.aeval (fun j => E (P (b.symm j))) ((M⁻¹).toMvPolynomial i)
    MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (Pc i)))) = {0} := by
  intro Pc
  have ht : (fun i => MvPolynomial.homogeneousComponent q (Pc i)) =
      (fun i => MvPolynomial.aeval
        (fun j => E (MvPolynomial.homogeneousComponent q (P (b.symm j)))) ((M⁻¹).toMvPolynomial i)) := by
    funext i
    rw [homogeneousComponent_matrix_polynomial_combination]
    exact congrArg (fun a => MvPolynomial.aeval a ((M⁻¹).toMvPolynomial i))
      (funext (fun j => hE (P (b.symm j))))
  rw [ht, polynomial_equation_coordinate_ideal E b M hM
    (fun i => MvPolynomial.homogeneousComponent q (P i))]
  exact polynomial_coordinate_origin_zeroLocus E h0 _ hz

/-- The actual origin-only highest system constructs exact degree q for
every equation; nonzero individual highest forms are NOT assumed. -/
theorem polynomial_equations_exact_degree_of_highest_zeroLocus
    {K : Type*} [Field K] [IsAlgClosed K] {n q : ℕ}
    (P : Fin n → MvPolynomial (Fin n) K)
    (hle : ∀ i, (P i).totalDegree ≤ q)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent q (P i)))) = {0}) :
    (∀ i, (P i).totalDegree = q) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K)
        (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))) := by
  let H := fun i => MvPolynomial.homogeneousComponent q (P i)
  have hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K) (List.ofFn H) :=
    homogeneous_origin_regular n H (fun i => ⟨q,MvPolynomial.homogeneousComponent_isHomogeneous q (P i)⟩) hz
  have hn (i : Fin n) : H i ≠ 0 :=
    regular_sequence_mem_ne_zero hreg (H i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hd (i : Fin n) : (P i).totalDegree = q :=
    le_antisymm (hle i) (Nat.le_of_not_lt fun h => hn i (MvPolynomial.homogeneousComponent_eq_zero q (P i) h))
  exact ⟨hd,by simpa only [hd] using hreg⟩

end LinearStudy
