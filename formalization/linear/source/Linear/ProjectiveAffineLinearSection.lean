module
public import Linear.ProjectiveSectionDefiningForms
public import Linear.ProjectiveAffineFiberUnit
public import Linear.ProjectiveLinearSectionEquationFibers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The actual linear-section equation ideal in the original X0=1 chart. -/
def projectiveAffineLinearSectionIdeal
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  V.affineIdeal ⊔ Ideal.span (Set.range (fun i =>
    affineChartPolynomialMap (projectiveLinearSectionForms L w i)))

/-- Homogeneous ideal equations remain zero under scalar normalization
over any coefficient algebra, including nonreduced quotient rings. -/
theorem homogeneousIdeal_aeval_scaled_zero {σ A : Type*}
    [CommRing A] [Algebra ℂ A]
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℂ))
    (v : σ → A) (hv : ∀ P ∈ I, MvPolynomial.aeval v P = 0) (a : A) :
    ∀ P ∈ I, MvPolynomial.aeval (fun i => a * v i) P = 0 := by
  intro P hP
  rw [← MvPolynomial.sum_homogeneousComponent P, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [homogeneous_aeval_smul (MvPolynomial.homogeneousComponent_isHomogeneous j P)]
  rw [hv _ (MvPolynomial.homogeneousComponent_mem_of_mem hI hP j), mul_zero]

/-- The normalization coordinate L0 is an actual unit in the affine
section quotient. Its nonvanishing is derived from finite normalization,
not assumed from equality of reduced point sets. -/
theorem projectiveAffineLinearSection_L0_isUnit
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (w : Fin (r+1) → ℂ) (hw0 : w 0 ≠ 0) :
    IsUnit (Ideal.Quotient.mk (projectiveAffineLinearSectionIdeal V L w)
      (affineChartPolynomialMap (L 0))) := by
  apply polynomialQuotient_isUnit_of_nonvanishing
  intro x hx hzero
  let v : CoordinateVector n := Fin.cases 1 x
  have hev (P : CoordinateRing n) :
      MvPolynomial.eval x (affineChartPolynomialMap P) = MvPolynomial.eval v P :=
    AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) x) P
  have hvI : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := by
    intro P hP
    rw [MvPolynomial.aeval_eq_eval]
    rw [← hev]
    exact hx _ (Ideal.mem_sup_left
      (Ideal.mem_map_of_mem affineChartPolynomialMap.toRingHom hP))
  have hvL (i : Fin (r+1)) : MvPolynomial.eval v (L i) = 0 := by
    cases i using Fin.cases with
    | zero => simpa only [hev] using hzero
    | succ i =>
      have he := hx _ (Ideal.mem_sup_right
        (Ideal.subset_span (Set.mem_range_self i)))
      rw [MvPolynomial.aeval_eq_eval] at he
      rw [hev] at he
      have hz : MvPolynomial.eval v (L 0) = 0 := by simpa only [hev] using hzero
      have hp : w 0 * MvPolynomial.eval v (L i.succ) = 0 := by
        simpa [projectiveLinearSectionForms, linearSectionSourceForms,
          MvPolynomial.aeval_def, ← MvPolynomial.eval_assoc, hz] using he
      exact (mul_eq_zero.mp hp).resolve_left hw0
  have hvzero := integral_linear_normalization_origin_zeroLocus V.ideal.toIdeal
    V.ideal.isHomogeneous L hL (projectiveLinearNormalizationMap V L)
    (fun _ => by simp [projectiveLinearNormalizationMap]) hfinite.to_isIntegral v hvI hvL
  have h01 := congrFun hvzero 0
  simpa [v] using h01

end LinearStudy
