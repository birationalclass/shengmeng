module
public import Linear.ActualEquationMaximalSocles
public import Linear.ProjectiveWholeFiberCommonSocle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4800000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- OUTPUT on the actual centered ambient equation algebra: the SAME
polynomial Jacobian covers EVERY maximal ideal, retaining normal nilpotents. -/
def ProjectiveWholeFiberMaximalSocleConclusion {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (r : ℕ) : Prop :=
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
      let A := MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range pC)
      let Θ : MvPolynomial (Fin r ⊕ Fin c) ℂ :=
        Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (pC (Sum.inr i)))
      Module.Finite ℂ A ∧
        ∀ (L : Ideal A) [L.IsMaximal],
          let t := algebraMap A (Localization.AtPrime L) (Ideal.Quotient.mk _ Θ)
          (nilradical (Localization.AtPrime L)).annihilator = Ideal.span {t} ∧ t ≠ 0

/-- Every maximal ideal is covered by an ORIGINAL source point: derive that
point from its actual scalar residue homomorphism and exact changed ideal.
Only the already proved geometric OUTPUTS are inputs. -/
theorem projective_actual_whole_fiber_maximal_socles {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hgeom : ProjectiveWholeAmbientFiberConclusion f V y hy r)
    (hcommon : ProjectiveWholeFiberCommonSocleConclusion f V y r) :
    ProjectiveWholeFiberMaximalSocleConclusion f V y r := by
  classical
  obtain ⟨c,hcr,hc,eS,MS,hMS,eT,MT,hMT,hFinite,hPoints⟩ := hcommon
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
  have hJ : J = (projectiveAmbientFiberIdeal f y).map E.toRingHom :=
    projective_actual_centered_fiber_ideal f y E eT.symm MT hMT
  have hZ := hgeom.2.2.1
  refine ⟨c,hcr,hc,eS,MS,hMS,eT,MT,hMT,hFinite,?_⟩
  apply polynomial_coordinate_socles_cover_maximal_ideals E
    (projectiveAmbientFiberIdeal f y) J hJ Θ
  intro x
  have hx : x.val ∈ MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) := by
    rw [← hZ]
    exact x.property
  exact hPoints ⟨x.val,hx⟩

/-- For EVERY original iterate, all maximal ideals of the SAME actual
ambient equation quotient have the constructed SAME nonzero Jacobian socle.
Positive actual chart dimension remains explicit. No local socle or
coverage assumption is an input; homogeneous relation is still OPEN. -/
theorem projective_iterates_whole_fibers_maximal_jacobian_socles {n : ℕ}
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
            ProjectiveWholeFiberMaximalSocleConclusion (f.iterate k) V y r := by
  obtain ⟨r,hrn,hdim,hrank,hiter⟩ := projective_iterates_whole_fibers_common_jacobian_socles
    f V hq hf hV hproper x0 hx0
  refine ⟨r,hrn,hdim,hrank,?_⟩
  intro k
  obtain ⟨p,hp,hnonempty,hfiber⟩ := hiter k
  refine ⟨p,hp,hnonempty,?_⟩
  intro y hy hyp hr
  obtain ⟨hgeom,hcommon⟩ := hfiber y hy hyp hr
  exact ⟨hgeom,projective_actual_whole_fiber_maximal_socles (f.iterate k) V y hy hgeom hcommon⟩

end LinearStudy
