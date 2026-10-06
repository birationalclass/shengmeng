module
public import Linear.PolynomialDiagonal
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# UniversalDifference

Construct an actual polynomial matrix in two independent sets of variables. Its diagonal specialization gives actual partial derivatives, and setting the right variables to zero gives a coefficient matrix for the equations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace LinearStudy
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def polynomialDoubleDiagonal : MvPolynomial (ι ⊕ ι) R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X MvPolynomial.X)

def polynomialDoubleRightZero : MvPolynomial (ι ⊕ ι) R →+* MvPowerSeries ι R :=
  MvPolynomial.eval₂Hom MvPowerSeries.C (Sum.elim MvPowerSeries.X (fun _ => 0))

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleDiagonal_left (P : MvPolynomial ι R) :
    polynomialDoubleDiagonal (MvPolynomial.rename Sum.inl P) = P := by
  have h : polynomialDoubleDiagonal.comp (MvPolynomial.rename Sum.inl).toRingHom =
      RingHom.id (MvPolynomial ι R) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;>
      simp [polynomialDoubleDiagonal]
  exact RingHom.congr_fun h P

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleRightZero_left (P : MvPolynomial ι R) :
    polynomialDoubleRightZero (MvPolynomial.rename Sum.inl P) = (P : MvPowerSeries ι R) := by
  have h : polynomialDoubleRightZero.comp (MvPolynomial.rename Sum.inl).toRingHom =
      (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial ι R →+* MvPowerSeries ι R) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;>
      simp [polynomialDoubleRightZero]
  exact RingHom.congr_fun h P

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleRightZero_right (P : MvPolynomial ι R) :
    polynomialDoubleRightZero (MvPolynomial.rename Sum.inr P) =
      MvPowerSeries.C P.constantCoeff := by
  have h : polynomialDoubleRightZero.comp (MvPolynomial.rename Sum.inr).toRingHom =
      (MvPowerSeries.C (σ := ι) (R := R)).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext <;> intro i <;>
      simp [polynomialDoubleRightZero]
  exact RingHom.congr_fun h P

theorem polynomial_universal_difference_matrix (P : ι → MvPolynomial ι R)
    (hzero : ∀ i, (P i).constantCoeff = 0) :
    ∃ D : Matrix ι ι (MvPolynomial (ι ⊕ ι) R),
      D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
        (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)) ∧
      (∀ i j, polynomialDoubleDiagonal (D i j) = MvPolynomial.pderiv j (P i)) ∧
      (D.map polynomialDoubleRightZero).mulVec MvPowerSeries.X =
        (fun i => (P i : MvPowerSeries ι R)) := by
  classical
  let u : MvPolynomial ι R →+* MvPolynomial (ι ⊕ ι) R :=
    (MvPolynomial.rename Sum.inl).toRingHom
  let v : MvPolynomial ι R →+* MvPolynomial (ι ⊕ ι) R :=
    (MvPolynomial.rename Sum.inr).toRingHom
  let π := polynomialDoubleDiagonal (R := R) (ι := ι)
  have hc : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c) := by
    intro c; simp [u, v]
  have hx : ∀ i, π (u (MvPolynomial.X i)) = π (v (MvPolynomial.X i)) := by
    intro i; simp [π, u, v, polynomialDoubleDiagonal]
  choose D hD hd using fun i => polynomial_diagonal_difference u v π hc hx (P i)
  let M : Matrix ι ι (MvPolynomial (ι ⊕ ι) R) := D
  have he : M.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
      (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)) := by
    funext i
    change (∑ j, D i j * (MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inr j))) = _
    simpa [u, v] using (hD i).symm
  refine ⟨M, he, ?_, ?_⟩
  · intro i j
    exact (hd i j).trans (polynomialDoubleDiagonal_left _)
  · funext i
    change (∑ j, polynomialDoubleRightZero (M i j) * MvPowerSeries.X j) = _
    have h := congrArg polynomialDoubleRightZero (congrFun he i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_sub,
      polynomialDoubleRightZero_left, polynomialDoubleRightZero_right, hzero,
      map_zero] at h
    simpa [polynomialDoubleRightZero, MvPolynomial.eval₂Hom_X,
      Matrix.map_apply, sub_zero] using h

end LinearStudy
