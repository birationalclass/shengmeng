module
public import Linear.HomogeneousCutAffineFinite
public import Linear.OriginalCutEquationZeroFiber
public import Linear.ProjectivePulledSectionNativeCoverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The ACTUAL map to the SAME original affine coordinate ring,defined
by the SAME pulled cut equations. It may depend on the chosen cut. -/
def projectivePulledCutEquationMap {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    MvPolynomial (Fin r) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :=
  (Ideal.Quotient.mkₐ ℂ V.affineIdeal).comp
    (MvPolynomial.aeval (fun i => affineChartPolynomialMap
      (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
/-- Original no-infinity of the SAME pulled cut derives finiteness of
its actual equation map. No finite/free/flat certificate is assumed. -/
theorem projectivePulledCutEquationMap_finite_of_original_no_infinity {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i,(L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (havoid : ∀ v : CoordinateVector n,
      v ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) →
      v ≠ 0 → v 0 ≠ 0) :
    (projectivePulledCutEquationMap f V L w).toRingHom.Finite := by
  have hno : ∀ z : CoordinateVector n,z ≠ 0 →
      z ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal → z 0=0 →
        ∃ i : Fin r,MvPolynomial.eval z
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)) ≠ 0 := by
    intro z hz hIz hz0
    by_contra! h
    have hcut : z ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) := by
      apply (show projectivePulledLinearSectionIdeal f V L w ≤
          RingHom.ker (MvPolynomial.aeval (R:=ℂ) z).toRingHom from ?_)
      apply sup_le hIz
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact h i
    exact havoid z hcut hz hz0
  let H : Fin r → MvPolynomial (Fin (n+1)) ℂ :=
    fun i => MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)
  have hH : ∀ i,(H i).IsHomogeneous f.degree :=
    projective_pulled_back_section_forms_homogeneous f L hL w
  let v : Fin (n+1) → ℂ := Fin.cases 1 x0
  have hv : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
    (V.normalizedPoint_mem_iff x0).mp hx0
  have result := @homogeneous_cut_no_infinity_actual_affine_map_finite
    ℂ inferInstance inferInstance n r f.degree V.ideal.toIdeal
    V.ideal.isHomogeneous v hv H hq hH hno
  exact result
/-- The ORIGINAL geometric Setup supplies the no-infinity open;hence
one nonempty original parameter open makes every actual equation map finite.
No independent generic-free open is introduced. -/
theorem projectivePulledCutEquationMap_exists_finite_open {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        (projectivePulledCutEquationMap f V L w).toRingHom.Finite := by
  obtain ⟨c,hc,hex,hcuts⟩ := projectivePulledLinearSection_exists_chart_avoidance_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨_,_,_,havoid⟩ := hcuts w hw
  exact projectivePulledCutEquationMap_finite_of_original_no_infinity
    f V hq L hL w x0 hx0 (fun v hv hvne => (havoid v hv hvne).1)
end LinearStudy
