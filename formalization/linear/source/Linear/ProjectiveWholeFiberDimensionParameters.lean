module
public import Linear.ProjectiveDifferentialDimension
public import Linear.ProjectiveWholeFiberKrullPower
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- ONE actual dimension controls both the whole original iterate fibers and
the number of actual polynomial local parameters at EVERY original smooth
chart point. No rank or fiber-cardinality formula is supplied as an input. -/
theorem projective_whole_fibers_and_smooth_parameters_same_dimension
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    ∃ r : ℕ, r ≤ n ∧ ringKrullDim B = (r : WithBot ℕ∞) ∧
      Module.finrank B (KaehlerDifferential ℂ B) = r ∧
      (∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
        Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal →
        let Q := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
        let J := V.affineIdeal.map (algebraMap _ (Localization.AtPrime Q))
        ∃ a : Fin r → MvPolynomial (Fin n) ℂ,
          Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
            (algebraMap _ (Localization.AtPrime Q) (a i)))) =
              (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk J)) ∧
      ∀ k : ℕ, ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
            Nat.card ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}) =
              (f.degree ^ k) ^ r := by
  intro B
  obtain ⟨r, hrn, hdim, hiter⟩ :=
    projective_iterates_whole_fiber_krull_power f V hq hf hV x0 hx0
  have hrank : Module.finrank B (KaehlerDifferential ℂ B) = r := by
    have h := (V.chart_krull_dimension_eq_differential_rank x0 hx0).symm.trans hdim
    exact_mod_cast h
  refine ⟨r, hrn, hdim, hrank, ?_, hiter⟩
  intro y hy hs Q J
  obtain ⟨s, a, hsRank, ha⟩ := V.smoothPoint_polynomial_parameters hproper y hy hs
  have hsr : s = r := hsRank.trans hrank
  clear hsRank
  subst s
  exact ⟨a, ha⟩

end LinearStudy
