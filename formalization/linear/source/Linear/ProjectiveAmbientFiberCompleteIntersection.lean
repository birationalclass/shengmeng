module
public import Linear.ProjectiveAmbientFiberHighest
public import Linear.AffineChartComparison
public import Linear.ProjectiveWholeFiberCommonCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual affine equations of the original ambient projective fiber. -/
def projectiveAmbientFiberPolynomials (f : HomogeneousEndomorphism n) (y : Fin n → ℂ) :
    Fin n → MvPolynomial (Fin n) ℂ :=
  fun i => affineChartPolynomialMap (projectiveAmbientFiberForms f y i)

theorem projectiveAmbientFiberIdeal_eq_polynomial_span
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ) :
    projectiveAmbientFiberIdeal f y = Ideal.span (Set.range (projectiveAmbientFiberPolynomials f y)) := by
  have heq : projectiveAmbientFiberPolynomials f y = (fun i : Fin n =>
      affineChartPolynomialMap (f.forms i.succ) -
        MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)) := by
    funext i
    simp only [projectiveAmbientFiberPolynomials, projectiveAmbientFiberForms,
      map_sub, map_mul]
    simp [affineChartPolynomialMap]
  unfold projectiveAmbientFiberIdeal
  rw [heq]

/-- This is the actual ambient equation system used for residues, rather
than the reduced in-V quotient. Highest-form regularity is constructed. -/
theorem projectiveAmbientFiberPolynomials_regular
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (y : Fin n → ℂ)
    (havoid : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) :
    let P := projectiveAmbientFiberPolynomials f y
    (∀ i, (P i).totalDegree = f.degree) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) ℂ)
        (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range (fun i =>
        MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0} := by
  simpa only [projectiveAmbientFiberPolynomials, affineChartPolynomialMap_eq_dehomogenize] using
    projectiveAmbientFiberForms_actual_highest_regular f hq y havoid

/-- Explicit output on one SAME original whole fiber. Finiteness of the
ambient algebra retains normal nilpotents; only its radical is compared. -/
def ProjectiveWholeAmbientFiberConclusion
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet) (r : ℕ) : Prop :=
  ProjectiveWholeFiberCommonCoordinateConclusion f V y hy r ∧
    Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAmbientFiberIdeal f y) ∧
    MvPolynomial.zeroLocus ℂ (projectiveAmbientFiberIdeal f y) =
      MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) ∧
    (projectiveAmbientFiberIdeal f y).radical = (projectiveAffineFiberIdeal f V y).radical ∧
    (let P := projectiveAmbientFiberPolynomials f y;
      (∀ i, (P i).totalDegree = f.degree) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) ℂ)
        (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range (fun i =>
        MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0})

/-- Every ORIGINAL iterate constructs a nonempty good open and the SAME
whole fiber with exact dimension, common local coordinates and an actual
finite ambient complete-intersection equation system of exact degree q.
No fiber data, leading-form regularity, degree or point-count formula are
assumed. The common normal Jacobian socle and homogeneous relation are NOT
claimed by this theorem. -/
theorem projective_iterates_whole_ambient_fibers_common_geometry
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      ∀ k : ℕ,
        let F := f.iterate k
        let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
        let A := Localization.Away (projectiveChartDenominator F V)
        let φ := projectiveChartOpenMap F V (f.iterate_degree_pos hq k)
          (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
        letI : Algebra B A := φ.toRingHom.toAlgebra
        ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal p) ∉ P.asIdeal →
          P ∈ Algebra.smoothLocus ℂ A ∧
          PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
          P ∈ Algebra.unramifiedLocus B A) ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          ProjectiveWholeAmbientFiberConclusion (f.iterate k) V y hy r := by
  obtain ⟨r, hrn, hdim, hrank, hiter⟩ :=
    projective_iterates_whole_fibers_actual_common_coordinates f V hq hf hV hproper x0 hx0
  refine ⟨r, hrn, hdim, hrank, ?_⟩
  intro k F B A φ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨p, hp, hgood, hnonempty, hfiber⟩ := hiter k
  refine ⟨p, hp, hgood, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨havoid, hcoords⟩ := hfiber y hy hyp
  refine ⟨hcoords, projectiveAmbientFiberQuotient_finite _ (f.iterate_degree_pos hq k) y,
    projectiveAmbientFiberIdeal_zeroLocus_eq_inside _ V (f.iterate_total_invariance V.zeroSet hV k) y hy,
    projectiveAmbientFiberIdeal_radical_eq_inside _ V (f.iterate_total_invariance V.zeroSet hV k) y hy,
    projectiveAmbientFiberPolynomials_regular _ (f.iterate_degree_pos hq k) y havoid⟩

end LinearStudy
