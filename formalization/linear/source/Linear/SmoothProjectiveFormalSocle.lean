module
public import Linear.FormalPullbackFiber
public import Linear.SmoothPolynomialFiber
public import Linear.FormalParameterFiber
public import Linear.SmoothNormalJacobian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
variable {r c : ℕ} [Nonempty (Fin c)]

def formalPolynomialAtPointUnit {K σ : Type*} [Field K] [Finite σ]
    (x : σ → K) (p : MvPolynomial σ K) (hp : MvPolynomial.eval x p ≠ 0) :
    (MvPowerSeries σ K)ˣ :=
  (show IsUnit (formalPolynomialAtPoint x p) from by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, formalPolynomialAtPoint_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hp).unit

theorem formalPolynomialAtPointUnit_coe {K σ : Type*} [Field K] [Finite σ]
    (x : σ → K) (p : MvPolynomial σ K) (hp : MvPolynomial.eval x p ≠ 0) :
    (formalPolynomialAtPointUnit x p hp : MvPowerSeries σ K) =
      formalPolynomialAtPoint x p := IsUnit.unit_spec _

def projectiveFormalCoordinateRatios
    (x : Fin r ⊕ Fin c → ℂ)
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ) :
    Fin r ⊕ Fin c → MvPowerSeries (Fin r ⊕ Fin c) ℂ :=
  fun i => ((formalPolynomialAtPointUnit x p0 hp0)⁻¹ :
    (MvPowerSeries (Fin r ⊕ Fin c) ℂ)ˣ) * formalPolynomialAtPoint x (p i)

omit [Nonempty (Fin c)] in
theorem projectiveFormalCoordinateRatios_constantCoeff
    (x : Fin r ⊕ Fin c → ℂ)
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0) (i : Fin r ⊕ Fin c) :
    (projectiveFormalCoordinateRatios x p0 hp0 p i).constantCoeff = 0 := by
  simp [projectiveFormalCoordinateRatios, formalPolynomialAtPoint_constantCoeff, hp]

def smoothProjectivePullbackEquations
    (x : Fin r ⊕ Fin c → ℂ)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) ℂ) : Fin c → AmbientRing r c :=
  fun i => polynomialSmoothAmbientEquiv x G hG hJac
    (MvPowerSeries.substAlgHom (R := ℂ) (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (projectiveFormalCoordinateRatios_constantCoeff x p0 hp0 p hp)) (H i))

def smoothProjectiveParameterLifts
    (x : Fin r ⊕ Fin c → ℂ)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ) : Fin r → AmbientRing r c :=
  fun i => polynomialSmoothAmbientEquiv x G hG hJac
    (projectiveFormalCoordinateRatios x p0 hp0 p (Sum.inl i))

theorem smooth_projective_full_fiber_ideal
    (x : Fin r ⊕ Fin c → ℂ)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) ℂ)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) ℂ)) ^ 2) :
    equationIdeal (smoothProjectivePullbackEquations x G hG hJac p0 hp0 p hp H) ⊔
      Ideal.span (Set.range (smoothProjectiveParameterLifts x G hG hJac p0 hp0 p)) =
        (Ideal.span (Set.range p)).map (polynomialSmoothFormalMap x G hG hJac) := by
  let E := polynomialSmoothAmbientEquiv x G hG hJac
  have h := formal_unit_divided_fiber_ideal
    (fun i => formalPolynomialAtPoint x (p i))
    (fun i => by rw [formalPolynomialAtPoint_constantCoeff]; exact hp i)
    (formalPolynomialAtPointUnit x p0 hp0) H hH
  have hh := congrArg (Ideal.map E.toRingHom) h
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Ideal.map_span,
    ← Set.range_comp, ← Set.range_comp, ← Set.range_comp] at hh
  rw [Ideal.map_span, ← Set.range_comp]
  exact (sup_comm _ _).trans hh

theorem smooth_projective_common_theta_formal_socle
    (x : Fin r ⊕ Fin c → ℂ)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) ℂ)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) ℂ)) ^ 2)
    (hr : 0 < r) (hc : 0 < c)
    (hrad : (equationIdeal (smoothProjectivePullbackEquations x G hG hJac p0 hp0 p hp H)).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))))
    (hτ : Ideal.span (Set.range (fun i =>
      (smoothProjectiveParameterLifts x G hG hJac p0 hp0 p i).constantCoeff)) =
        IsLocalRing.maximalIdeal (ParameterRing r)) :
    let ψ := polynomialSmoothFormalMap x G hG hJac
    let J := (Ideal.span (Set.range p)).map ψ
    let Θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (p (Sum.inr i)))
    (nilradical (AmbientRing r c ⧸ J)).annihilator =
      Ideal.span {Ideal.Quotient.mk J (ψ Θ)} ∧ Ideal.Quotient.mk J (ψ Θ) ≠ 0 := by
  intro ψ J Θ
  let L := smoothProjectivePullbackEquations x G hG hJac p0 hp0 p hp H
  let τ := smoothProjectiveParameterLifts x G hG hJac p0 hp0 p
  let Δ := Matrix.det (fun i j => MvPowerSeries.pderiv j (L i))
  have hm : equationIdeal L ⊔ Ideal.span (Set.range τ) = J :=
    smooth_projective_full_fiber_ideal x G hG hJac p0 hp0 p hp H hH
  obtain ⟨hArt, hgen, hne⟩ := formal_parameter_fiber_jacobian_socle L hr hc hrad τ hτ
  let E0 := Ideal.quotEquivOfEq hm
  have he (z : AmbientRing r c) :
      E0 (Ideal.Quotient.mk (equationIdeal L ⊔ Ideal.span (Set.range τ)) z) =
        Ideal.Quotient.mk J z := Ideal.quotEquivOfEq_mk _ z
  have hgenJ : (nilradical (AmbientRing r c ⧸ J)).annihilator =
      Ideal.span {Ideal.Quotient.mk J Δ} := by
    have h := ringEquiv_nilradical_annihilator_generator
      (C := AmbientRing r c ⧸ J) E0 Δ hgen
    rwa [he] at h
  have hneJ : Ideal.Quotient.mk J Δ ≠ 0 := by
    rw [← he]
    intro hz
    exact hne (E0.injective (hz.trans E0.map_zero.symm))
  let E := polynomialSmoothAmbientEquiv x G hG hJac
  let u := Units.map E.toRingHom.toMonoidHom (formalPolynomialAtPointUnit x p0 hp0)
  have hfirst : ∀ i, L i - (u⁻¹ : (AmbientRing r c)ˣ) * ψ (p (Sum.inr i)) ∈ J ^ 2 := by
    have hJE : J = Ideal.span (Set.range (fun i => E (formalPolynomialAtPoint x (p i)))) := by
      dsimp only [J]
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hJE]
    have hh := formal_unit_divided_transformed_firstOrder
      (fun i => formalPolynomialAtPoint x (p i))
      (fun i => by rw [formalPolynomialAtPoint_constantCoeff]; exact hp i)
      (formalPolynomialAtPointUnit x p0 hp0) H hH E.toRingHom
    intro i
    have hi := hh i
    change L i - E ((formalPolynomialAtPointUnit x p0 hp0)⁻¹ :
      (MvPowerSeries (Fin r ⊕ Fin c) ℂ)ˣ) * ψ (p (Sum.inr i)) ∈
        (Ideal.span (Set.range (fun j => E (formalPolynomialAtPoint x (p j))))) ^ 2 at hi
    exact hi
  have hpJ : ∀ i, ψ (p (Sum.inr i)) ∈ J := by
    intro i
    exact Ideal.mem_map_of_mem ψ Ideal.mem_span_range_self
  have hfac := fiber_jacobian_unit_factor
    (fun j => MvPowerSeries.pderiv j) J u L (fun i => ψ (p (Sum.inr i))) hpJ hfirst
  rw [smooth_normal_jacobian_det_factor, map_mul] at hfac
  have hunit₁ : IsUnit ((Ideal.Quotient.mk J (u⁻¹ : (AmbientRing r c)ˣ)) ^ Fintype.card (Fin c)) :=
    ((Ideal.Quotient.mk J).isUnit_map (u⁻¹).isUnit).pow _
  have hunit₂ : IsUnit (Ideal.Quotient.mk J (Matrix.det
      (smoothNormalCoordinateJacobian x G hG hJac))) :=
    (Ideal.Quotient.mk J).isUnit_map (smooth_normal_coordinate_jacobian_det_unit x G hG hJac)
  refine ⟨?_, ?_⟩
  · rw [hgenJ, hfac, Ideal.span_singleton_mul_left_unit hunit₁,
      Ideal.span_singleton_mul_right_unit hunit₂]
  · intro hz
    apply hneJ
    change Ideal.Quotient.mk J (Matrix.det (fun i j => MvPowerSeries.pderiv j (L i))) = 0
    rw [hfac, hz, zero_mul, mul_zero]

theorem smooth_projective_common_theta_local_socle
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    [IsArtinianRing (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range p))]
    (q : (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range p)) →ₐ[ℂ] ℂ)
    (x : Fin r ⊕ Fin c → ℂ)
    (hx : x = fun i => q (Ideal.Quotient.mk (Ideal.span (Set.range p)) (MvPolynomial.X i)))
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0)
    (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) ℂ)
    (hH : ∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) ℂ)) ^ 2)
    (hr : 0 < r) (hc : 0 < c)
    (hrad : (equationIdeal (smoothProjectivePullbackEquations x G hG hJac p0 hp0 p hp H)).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))))
    (hτ : Ideal.span (Set.range (fun i =>
      (smoothProjectiveParameterLifts x G hG hJac p0 hp0 p i).constantCoeff)) =
        IsLocalRing.maximalIdeal (ParameterRing r)) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let Θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (p (Sum.inr i)))
    let a := algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range p))
      (Localization.AtPrime (RingHom.ker q.toRingHom))
        (Ideal.Quotient.mk (Ideal.span (Set.range p)) Θ)
    (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
      Ideal.span {a} ∧ a ≠ 0 := by
  subst x
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x := fun i => q (Ideal.Quotient.mk (Ideal.span (Set.range p)) (MvPolynomial.X i))
  let Θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (p (Sum.inr i)))
  obtain ⟨hgen, hne⟩ := smooth_projective_common_theta_formal_socle
    x G hG hJac p0 hp0 p hp H hH hr hc hrad hτ
  have hlocal := smooth_polynomial_formal_socle_generator_descends
    (Ideal.span (Set.range p)) q G hG hJac Θ hgen
  refine ⟨hlocal, ?_⟩
  let A := AmbientRing r c ⧸ (Ideal.span (Set.range p)).map (polynomialSmoothFormalMap x G hG hJac)
  let E : A ≃+* Localization.AtPrime (RingHom.ker q.toRingHom) :=
    smoothPolynomialFormalFiberEquiv (Ideal.span (Set.range p)) q G hG hJac
  have he := smoothPolynomialFormalFiberEquiv_polynomial (Ideal.span (Set.range p)) q G hG hJac Θ
  change E (Ideal.Quotient.mk _ (polynomialSmoothFormalMap x G hG hJac Θ)) = _ at he
  rw [← he]
  intro hz
  exact hne (E.injective (hz.trans E.map_zero.symm))

end LinearStudy
