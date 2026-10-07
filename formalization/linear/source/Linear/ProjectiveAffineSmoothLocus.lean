module
public import Linear.ProjectiveAffinePointData
public import Linear.SmoothLocusCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

def IntegralProjectiveEquations.affinePoint
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :=
  ⟨V.affinePointIdeal x, V.affinePointIdeal_isPrime x hx⟩

/-- Actual smooth affine points of the original integral projective variety
construct common ambient coordinates and formal normal ideals. No separate
prime ideal or point-kernel comparison is supplied as a hypothesis. -/
theorem projective_affine_smooth_points_have_common_formal_coordinates
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : IntegralProjectiveEquations n) (hV : V.ideal.toIdeal ≠ ⊥)
    (x : ι → Fin n → ℂ) (hx : ∀ a, normalizedProjectivePoint (x a) ∈ V.zeroSet)
    [∀ a, Algebra.IsSmoothAt ℂ (V.affinePoint (x a) (hx a)).asIdeal] :
    ∃ (r c : ℕ) (hc : 0 < c),
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ Fin n)
        (M : Matrix (Fin n) (Fin n) ℂ) (hM : Matrix.det M ≠ 0)
        (G : ι → Fin c → MvPolynomial (Fin n) ℂ),
        let C := polynomialLinearChangeEquiv M hM
        let y : ι → Fin r ⊕ Fin c → ℂ := fun a => (M⁻¹ *ᵥ x a) ∘ e
        let H : ι → Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
          fun a i => MvPolynomial.rename e.symm (C (G a i))
        ∃ (hH : ∀ a i, MvPolynomial.eval (y a) (H a i) = 0)
          (hJ : ∀ a, IsUnit (Matrix.det (fun i j => MvPolynomial.eval (y a)
            (MvPolynomial.pderiv (Sum.inr j) (H a i))))),
          ∀ a, V.affineIdeal.map
            (((polynomialSmoothFormalMap (y a) (H a) (hH a) (hJ a)).comp
              (MvPolynomial.rename e.symm).toRingHom).comp C.toRingHom) =
            Ideal.span (Set.range (MvPowerSeries.X
              (σ := Fin c) (R := MvPowerSeries (Fin r) ℂ))) := by
  let a := Classical.choice (inferInstance : Nonempty ι)
  letI : V.affineIdeal.IsPrime := V.affineIdeal_isPrime_of_point (x a) (hx a)
  let p := fun a => (V.affinePoint (x a) (hx a)).asIdeal
  have hp : ∀ a, (p a).comap (Ideal.Quotient.mk V.affineIdeal) =
      RingHom.ker (MvPolynomial.aeval (R := ℂ) (x a)).toRingHom := by
    intro a
    exact V.affinePointIdeal_comap (x a) (hx a)
  exact smoothLocus_prime_points_have_common_formal_normal_coordinates
    V.affineIdeal (V.affineIdeal_ne_bot hV) p x hp

end LinearStudy
