module
public import Linear.ProjectiveCutEquationFiberLocalData
public import Linear.PolynomialPointOriginalFiberTrace
public import Linear.ChosenProjectiveNormalizationDimensions
public import Linear.ProjectivePulledSectionSmoothPoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory TensorProduct
/-- Statement for the ACTUAL cut-dependent equation-map coefficient dual.
The projector is the existing original scalar projector and the trace is
LITERAL base change of eval at1. This definition is not a proof and does
not identify this dual with the FIXED original normalization coefficient. -/
def projectivePulledCutEquationTraceOneStatement {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) : Prop :=
  let R := MvPolynomial (Fin r) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let phi := projectivePulledCutEquationMap f V L w
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom.toAlgebra
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  ∀ e : ℂ ⊗[R] B,e ≠ 0 → e*e=e →
    ∃ z : ℂ ⊗[R] ((ModuleCat.restrictScalars (algebraMap R B)).obj
      ((ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R))),
      coextensionOriginalResidueFiberPointEnd
        (show Function.Surjective (algebraMap R ℂ) from
          fun a => ⟨MvPolynomial.C a,by
            change (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)) (MvPolynomial.C a)=a
            exact (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).commutes a⟩) e z=z ∧
        coextensionOriginalBaseChangedEvaluationAtOne (R:=R) (S:=B) (K:=ℂ) z=1
/-- Original finite reduced smooth cut DERIVES every local input and
trace1 on each nonzero actual fiber idempotent for the actual equation
map. The equation map is explicitly finite;global free/flat/CM are not inputs. -/
theorem projectivePulledCutEquation_trace_one_of_original_smooth_cut {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)=(r : WithBot ℕ∞))
    (hfinite : (projectivePulledCutEquationMap f V L w).toRingHom.Finite)
    (hsmooth : ∀ x : Fin n → ℂ,x ∈ MvPolynomial.zeroLocus ℂ
      ((projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom) →
      ∃ hxV : normalizedProjectivePoint x ∈ V.zeroSet,
        Algebra.IsSmoothAt ℂ (V.affinePoint x hxV).asIdeal)
    [IsReduced (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom)]
    [Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom)] :
    projectivePulledCutEquationTraceOneStatement f V L w := by
  let R := MvPolynomial (Fin r) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let phi := projectivePulledCutEquationMap f V L w
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  haveI : Module.Finite R B := RingHom.finite_algebraMap.mp hfinite
  unfold projectivePulledCutEquationTraceOneStatement
  dsimp only
  apply polynomial_point_original_coextension_trace_one_of_original_fiber (K:=ℂ) (S:=B) (0 : Fin r → ℂ)
  · change IsReduced (B ⧸ (RingHom.ker
      (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom).map phi.toRingHom)
    have he : phi=MvPolynomial.aeval (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))) := by
      dsimp only [phi,projectivePulledCutEquationMap]
      simpa only [Ideal.Quotient.mkₐ_eq_mk] using
        (MvPolynomial.comp_aeval (f:=fun i : Fin r => affineChartPolynomialMap
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
          (Ideal.Quotient.mkₐ ℂ V.affineIdeal))
    rw [he]
    exact projectivePulledCutEquation_zero_fiber_reduced f V L w
  · exact projectivePulledCutEquation_zeroFiber_all_point_local_data f V hproper L w hdim hsmooth
/-- The complete ORIGINAL geometric Setup DERIVES one nonempty original
parameter open with finite ACTUAL equation map and literal trace1 on every
nonzero fiber idempotent. Local CM/dimension/reducedness are DERIVED.
This joins actual original cut points to the equation-map coextension.
Comparison with the FIXED normalization dual and SAME top-H remain OPEN. -/
theorem projectivePulledCutEquation_originalSetup_exists_trace_one_open {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        (projectivePulledCutEquationMap f V L w).toRingHom.Finite ∧
        projectivePulledCutEquationTraceOneStatement f V L w := by
  obtain ⟨a,ha,_,hfiniteA⟩ := projectivePulledCutEquationMap_exists_finite_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨b,hb,_,hcuts⟩ := projectivePulledLinearSection_exists_smooth_finite_reduced_cuts
    f V hq hf hV L hL hinj hfinite x0 hx0
  have hc : a*b ≠ 0 := mul_ne_zero ha hb
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (a*b) ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (MvPolynomial.funext (fun w => by simpa using h w))
  refine ⟨a*b,hc,hex,?_⟩
  intro w hw
  obtain ⟨hwa,hwb⟩ := mul_ne_zero_iff.mp (by simpa only [MvPolynomial.eval_mul] using hw)
  obtain ⟨_,hred,hfin,_,_,hsmooth⟩ := hcuts w hwb
  letI := hred
  letI := hfin
  exact ⟨hfiniteA w hwa,projectivePulledCutEquation_trace_one_of_original_smooth_cut f V
    (chosenProjectiveNormalization_definingIdeal_ne_bot V L hinj hfinite hrn) L w
    (chosenProjectiveNormalization_chart_dimension V L hinj hfinite x0 hx0)
    (hfiniteA w hwa) hsmooth⟩
end LinearStudy
