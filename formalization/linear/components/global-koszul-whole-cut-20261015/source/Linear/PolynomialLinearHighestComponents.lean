module
public import Linear.PolynomialLinearGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- A genuinely grading-preserving polynomial algebra map commutes with
each actual homogeneous component; proved from the finite decomposition. -/
theorem polynomial_grading_map_homogeneousComponent
    {K σ τ : Type*} [CommRing K]
    (E : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hE : ∀ (d : ℕ) (P : MvPolynomial σ K),
      P.IsHomogeneous d → (E P).IsHomogeneous d)
    (q : ℕ) (G : MvPolynomial σ K) :
    MvPolynomial.homogeneousComponent q (E G) =
      E (MvPolynomial.homogeneousComponent q G) := by
  classical
  have hpart (i : ℕ) :
      MvPolynomial.homogeneousComponent q (E (MvPolynomial.homogeneousComponent i G)) =
        E (MvPolynomial.homogeneousComponent q (MvPolynomial.homogeneousComponent i G)) := by
    rw [MvPolynomial.homogeneousComponent_of_mem
      (hE i _ (MvPolynomial.homogeneousComponent_isHomogeneous i G)),
      MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.homogeneousComponent_isHomogeneous i G)]
    split_ifs <;> simp
  calc
    MvPolynomial.homogeneousComponent q (E G) =
        ∑ i ∈ Finset.range (G.totalDegree+1),
          MvPolynomial.homogeneousComponent q (E (MvPolynomial.homogeneousComponent i G)) := by
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent G, map_sum, map_sum]
    _ = ∑ i ∈ Finset.range (G.totalDegree+1),
        E (MvPolynomial.homogeneousComponent q (MvPolynomial.homogeneousComponent i G)) := by
      exact Finset.sum_congr rfl (fun i _ => hpart i)
    _ = E (MvPolynomial.homogeneousComponent q G) := by
      rw [← map_sum, ← map_sum, MvPolynomial.sum_homogeneousComponent G]

theorem polynomialLinearChange_homogeneousComponent
    {K σ : Type*} [CommRing K] [Fintype σ]
    (M : Matrix σ σ K) (q : ℕ) (G : MvPolynomial σ K) :
    MvPolynomial.homogeneousComponent q (polynomialLinearChange M G) =
      polynomialLinearChange M (MvPolynomial.homogeneousComponent q G) :=
  polynomial_grading_map_homogeneousComponent (polynomialLinearChange M)
    (fun _ _ h => polynomialLinearChange_isHomogeneous M h) q G

theorem polynomialLinearChangeEquiv_homogeneousComponent
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0) (q : ℕ) (G : MvPolynomial σ K) :
    MvPolynomial.homogeneousComponent q (polynomialLinearChangeEquiv M hM G) =
      polynomialLinearChangeEquiv M hM (MvPolynomial.homogeneousComponent q G) :=
  polynomialLinearChange_homogeneousComponent M q G

theorem polynomial_linear_reindex_homogeneousComponent
    {K σ τ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0) (e : σ ≃ τ)
    (q : ℕ) (G : MvPolynomial σ K) :
    let E := (polynomialLinearChangeEquiv M hM).trans (MvPolynomial.renameEquiv K e)
    MvPolynomial.homogeneousComponent q (E G) =
      E (MvPolynomial.homogeneousComponent q G) := by
  intro E
  change MvPolynomial.homogeneousComponent q
    (MvPolynomial.rename e (polynomialLinearChangeEquiv M hM G)) =
      MvPolynomial.rename e (polynomialLinearChangeEquiv M hM (MvPolynomial.homogeneousComponent q G))
  rw [← MvPolynomial.rename_homogeneousComponent, polynomialLinearChangeEquiv_homogeneousComponent]

end LinearStudy
