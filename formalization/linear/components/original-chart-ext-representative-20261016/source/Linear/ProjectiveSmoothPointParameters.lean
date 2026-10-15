module
public import Linear.SmoothTargetParameters
public import Linear.LocalQuotientMaximalIdeal
public import Linear.ProjectiveAffineVariety
public import Linear.ProjectiveAffineSmoothPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- At an actual smooth point of a proper integral projective variety,
target polynomial parameters are constructed from the original equations. -/
theorem IntegralProjectiveEquations.smoothPoint_polynomial_parameters
    (V : IntegralProjectiveEquations n) (hproper : V.ideal.toIdeal ≠ ⊥)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hs : Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal) :
    let P := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
    let J := V.affineIdeal.map (algebraMap _ (Localization.AtPrime P))
    ∃ (r : ℕ) (a : Fin r → MvPolynomial (Fin n) ℂ),
      r = Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) ∧
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime P) (a i)))) =
          (P.map (algebraMap _ (Localization.AtPrime P))).map (Ideal.Quotient.mk J) := by
  intro P
  intro J
  letI : V.affineIdeal.IsPrime := V.affineIdeal_isPrime_of_point y hy
  let p := (V.affinePoint y hy).asIdeal
  letI : p.IsPrime := inferInstance
  letI : Algebra.IsSmoothAt ℂ p := hs
  have hp : p.comap (Ideal.Quotient.mk V.affineIdeal) =
      RingHom.ker (MvPolynomial.aeval (R := ℂ) y).toRingHom :=
    V.affinePointIdeal_comap y hy
  let Q := p.comap (Ideal.Quotient.mk V.affineIdeal)
  letI : Q.IsPrime := inferInstance
  have hIQ : V.affineIdeal ≤ Q := by
    intro F hF
    change Ideal.Quotient.mk V.affineIdeal F ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
    exact p.zero_mem
  let L := V.affineIdeal.map (algebraMap _ (Localization.AtPrime Q))
  letI : Nontrivial (Localization.AtPrime Q ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top V.affineIdeal Q hIQ)
  letI : IsLocalRing (Localization.AtPrime Q ⧸ L) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  obtain ⟨r, a, hr, ha⟩ := smoothLocus_constructs_original_polynomial_parameters
    V.affineIdeal (V.affineIdeal_ne_bot hproper) p y hp
  have hm := ha.trans (point_local_quotient_maximalIdeal_map V.affineIdeal Q).symm
  refine ⟨r, a, hr, ?_⟩
  exact hm

end LinearStudy
