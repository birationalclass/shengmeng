module
public import Linear.ProjectiveWholeFiberMaximalSocle
public import Linear.ProjectiveCenteredFiberHighest
public import Linear.PolynomialNormalJacobianDegree
public import Linear.LocalizedAnnihilator
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4800000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Derived OUTPUT, on one same original whole fiber and the same actual
source/target coordinates: finite equation algebra, highest system,
fixed normal Jacobian degree bound and global nilradical annihilator.
The equation algebra retains its actual normal nilpotents. -/
def ProjectiveWholeFiberJacobianSystemConclusion {n : ℕ}
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ) (r : ℕ) : Prop :=
  ∃ c : ℕ, c = n-r ∧ 0 < c ∧
    ∃ (eS : (Fin r ⊕ Fin c) ≃ Fin n)
      (MS : Matrix (Fin n) (Fin n) ℂ) (hMS : Matrix.det MS ≠ 0)
      (eT : (Fin r ⊕ Fin c) ≃ Fin n)
      (MT : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) ℂ) (hMT : Matrix.det MT ≠ 0),
    let E := (polynomialLinearChangeEquiv MS hMS).trans (MvPolynomial.renameEquiv ℂ eS.symm)
    let z := MT⁻¹ *ᵥ (y ∘ eT)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      fun j => E (affineChartPolynomialMap (f.forms (eT j).succ))
    let pC : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      fun i => MvPolynomial.aeval p ((MT⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
    let J := Ideal.span (Set.range pC)
    let A := MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ J
    let Θ : MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (pC (Sum.inr i)))
    Module.Finite ℂ A ∧
      (∀ i, (pC i).totalDegree ≤ f.degree) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range
        (fun i => MvPolynomial.homogeneousComponent f.degree (pC i)))) = {0} ∧
      Θ.totalDegree ≤ c*(f.degree-1) ∧
      (nilradical A).annihilator = Ideal.span {Ideal.Quotient.mk J Θ}

/-- Combine already DERIVED original whole-fiber outputs. No highest,
Jacobian degree or global annihilator assumption is added. -/
theorem projective_actual_whole_fiber_jacobian_system {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hgeom : ProjectiveWholeAmbientFiberConclusion f V y hy r)
    (hmax : ProjectiveWholeFiberMaximalSocleConclusion f V y r) :
    ProjectiveWholeFiberJacobianSystemConclusion f y r := by
  classical
  obtain ⟨c,hcr,hc,eS,MS,hMS,eT,MT,hMT,hFinite,hLocal⟩ := hmax
  let E := (polynomialLinearChangeEquiv MS hMS).trans (MvPolynomial.renameEquiv ℂ eS.symm)
  let z := MT⁻¹ *ᵥ (y ∘ eT)
  let p0 := E (affineChartPolynomialMap (f.forms 0))
  let p : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
    fun j => E (affineChartPolynomialMap (f.forms (eT j).succ))
  let pC : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
    fun i => MvPolynomial.aeval p ((MT⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
  let J := Ideal.span (Set.range pC)
  let A := MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ J
  let Θ : MvPolynomial (Fin r ⊕ Fin c) ℂ :=
    Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (pC (Sum.inr i)))
  letI : Module.Finite ℂ A := hFinite
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite ℂ A
  obtain ⟨hdeg,_,hz⟩ := hgeom.2.2.2.2
  simp only [hdeg] at hz
  obtain ⟨hle,hTop⟩ := projective_linear_centered_fiber_highest f y MS hMS eS eT MT hMT hdeg hz
  have hbound : Θ.totalDegree ≤ c*(f.degree-1) :=
    polynomial_normal_jacobian_totalDegree pC hle
  have hgen : (nilradical A).annihilator = Ideal.span {Ideal.Quotient.mk J Θ} := by
    apply nilradical_annihilator_generator_of_localizations
    intro L hL
    exact (hLocal L).1
  exact ⟨c,hcr,hc,eS,MS,hMS,eT,MT,hMT,hFinite,hle,hTop,hbound,hgen⟩

/-- Every original iterate supplies the same equation/Jacobian system on
each target in a nonempty good open. Actual positive chart dimension is
explicit. No homogeneous projective relation is claimed yet. -/
theorem projective_iterates_whole_fibers_jacobian_system {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      ∀ k : ℕ,
        ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 → 0 < r →
          ProjectiveWholeAmbientFiberConclusion (f.iterate k) V y hy r ∧
            ProjectiveWholeFiberJacobianSystemConclusion (f.iterate k) y r := by
  obtain ⟨r,hrn,hdim,hrank,hiter⟩ := projective_iterates_whole_fibers_maximal_jacobian_socles
    f V hq hf hV hproper x0 hx0
  refine ⟨r,hrn,hdim,hrank,?_⟩
  intro k
  obtain ⟨p,hp,hnonempty,hfiber⟩ := hiter k
  refine ⟨p,hp,hnonempty,?_⟩
  intro y hy hyp hr
  obtain ⟨hgeom,hmax⟩ := hfiber y hy hyp hr
  exact ⟨hgeom,projective_actual_whole_fiber_jacobian_system (f.iterate k) V y hy hgeom hmax⟩

end LinearStudy
