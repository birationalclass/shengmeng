module
public import Linear.PolynomialLinearChange
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

theorem polynomialLinearChange_isHomogeneous {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) {G : MvPolynomial σ K} {q : ℕ} (hG : G.IsHomogeneous q) :
    (polynomialLinearChange P G).IsHomogeneous q := by
  simpa only [one_mul, polynomialLinearChange, MvPolynomial.bind₁,
    MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] using
    hG.eval₂ MvPolynomial.C P.toMvPolynomial (fun a => MvPolynomial.isHomogeneous_C _ a)
      (Matrix.toMvPolynomial_isHomogeneous P)

theorem polynomialLinearChangeEquiv_isHomogeneous {K σ : Type*}
    [Field K] [Fintype σ] [DecidableEq σ]
    (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0) {G : MvPolynomial σ K} {q : ℕ} :
    (polynomialLinearChangeEquiv P hP G).IsHomogeneous q ↔ G.IsHomogeneous q := by
  constructor
  · intro h
    have hh := polynomialLinearChange_isHomogeneous P⁻¹ h
    have he : polynomialLinearChange P⁻¹ (polynomialLinearChangeEquiv P hP G) = G :=
      (polynomialLinearChangeEquiv P hP).symm_apply_apply G
    rwa [he] at hh
  · exact polynomialLinearChange_isHomogeneous P

theorem homogeneous_linear_change_totalDegree {K σ : Type*}
    [Field K] [Fintype σ] [DecidableEq σ]
    (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0) {G : MvPolynomial σ K} {q : ℕ}
    (hG : G.IsHomogeneous q) (h0 : G ≠ 0) :
    (polynomialLinearChangeEquiv P hP G).totalDegree = q := by
  apply (polynomialLinearChange_isHomogeneous P hG).totalDegree
  intro hz
  exact h0 ((polynomialLinearChangeEquiv P hP).injective
    (hz.trans (map_zero (polynomialLinearChangeEquiv P hP)).symm))

theorem polynomialLinearChange_totalDegree_le {K σ : Type*} [CommRing K] [Fintype σ]
    (P : Matrix σ σ K) (G : MvPolynomial σ K) :
    (polynomialLinearChange P G).totalDegree ≤ G.totalDegree := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent G, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (polynomialLinearChange_isHomogeneous P
    (MvPolynomial.homogeneousComponent_isHomogeneous i G)).totalDegree_le.trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem polynomialLinearChangeEquiv_totalDegree {K σ : Type*}
    [Field K] [Fintype σ] [DecidableEq σ]
    (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0) (G : MvPolynomial σ K) :
    (polynomialLinearChangeEquiv P hP G).totalDegree = G.totalDegree := by
  apply le_antisymm (polynomialLinearChange_totalDegree_le P G)
  have h := polynomialLinearChange_totalDegree_le P⁻¹ (polynomialLinearChangeEquiv P hP G)
  have he : polynomialLinearChange P⁻¹ (polynomialLinearChangeEquiv P hP G) = G :=
    (polynomialLinearChangeEquiv P hP).symm_apply_apply G
  rwa [he] at h

end LinearStudy
