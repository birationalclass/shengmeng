module
public import Linear.OriginalCutEquationTensorFiber
public import Linear.PolynomialPointOriginalFiberDual
public import Linear.ProjectiveCutEquationPointTrace
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory TensorProduct
/-- ACTUAL original equation-coefficient fiber duality to the SAME original
cut ring. Statement definition only,not a proof. Pure values,LITERAL eval1
trace,and ORIGINAL source scalar action are required explicitly. The
coefficient is cut-dependent;FIXED normalization/top-H comparison OPEN. -/
def projectivePulledCutEquationCoefficientFiberDualStatement {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) : Prop :=
    let R := MvPolynomial (Fin r) ℂ
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let J := (projectivePulledLinearSectionIdeal f V L w).map
      (affineChartPolynomialMap (K:=ℂ)).toRingHom
    let Q := MvPolynomial (Fin n) ℂ ⧸ J
    let phi := projectivePulledCutEquationMap f V L w
    letI : Algebra R B := phi.toRingHom.toAlgebra
    letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
    letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
    letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom.toAlgebra
    let C := (ModuleCat.restrictScalars (algebraMap R B)).obj
      ((ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R))
    ∃ E : (ℂ ⊗[R] C) ≃ₗ[ℂ] Module.Dual ℂ Q,
      (∀ (a : ℂ) (ell : C) (P : MvPolynomial (Fin n) ℂ),
        E (a ⊗ₜ[R] ell) (Ideal.Quotient.mk J P)=
          a*algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B) ell)
            (Ideal.Quotient.mk V.affineIdeal P))) ∧
      (∀ z,E z 1=coextensionOriginalBaseChangedEvaluationAtOne z) ∧
      (∀ (P : MvPolynomial (Fin n) ℂ) z q,
        E (coextensionOriginalScalarFiberEnd (R:=R) (K:=ℂ)
          (Ideal.Quotient.mk V.affineIdeal P) z) q=
        E z (q*Ideal.Quotient.mk J P))
/-- From the ACTUAL original smooth finite reduced cut,construct an actual
field-linear equivalence from its actual equation-coefficient fiber to
the dual of the SAME original cut ring. Every original value and the
LITERAL trace and original source-action square are PROVED. -/
theorem projectivePulledCutEquation_coefficient_fiber_dual_of_smooth_cut {n r : ℕ}
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
    projectivePulledCutEquationCoefficientFiberDualStatement f V L w := by
  let R := MvPolynomial (Fin r) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let phi := projectivePulledCutEquationMap f V L w
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom.toAlgebra
  haveI : Module.Finite R B := RingHom.finite_algebraMap.mp hfinite
  have hred : IsReduced (B ⧸ (RingHom.ker
      (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom).map phi.toRingHom) := by
    rw [projectivePulledCutEquationMap_zero_fiber_ideal]
    let E := projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w
    exact isReduced_of_injective E.toRingHom E.injective
  have hgeom := projectivePulledCutEquation_zeroFiber_all_point_local_data
    f V hproper L w hdim hsmooth
  obtain ⟨Phi,hpure,hunit,hscalar⟩ := polynomial_point_original_fiber_dual_exists
    (K:=ℂ) (S:=B) (0 : Fin r → ℂ) hred hgeom
  let T := projectivePulledCutEquationTensorFiberEquiv f V L w
  unfold projectivePulledCutEquationCoefficientFiberDualStatement
  dsimp only
  refine ⟨Phi.trans (Module.Dual.congr T.toLinearEquiv),?_,?_,?_⟩
  · intro a ell P
    change Phi (a ⊗ₜ[R] ell) (T.symm (Ideal.Quotient.mk _ P))=_
    have hP : T.symm (Ideal.Quotient.mk _ P)=
        ((1:ℂ) ⊗ₜ[R] (Ideal.Quotient.mk V.affineIdeal P)) :=
      T.symm_apply_eq.mpr (projectivePulledCutEquationTensorFiberEquiv_tmul f V L w P).symm
    rw [hP]
    exact hpure a ell (Ideal.Quotient.mk V.affineIdeal P)
  · intro z
    change Phi z (T.symm 1)=_
    rw [map_one]
    exact hunit z
  · intro P z q
    change Phi (coextensionOriginalScalarFiberEnd (R:=R) (K:=ℂ)
      (Ideal.Quotient.mk V.affineIdeal P) z) (T.symm q)=
        Phi z (T.symm (q*Ideal.Quotient.mk _ P))
    rw [hscalar, map_mul T.symm]
    have hP : T.symm (Ideal.Quotient.mk _ P)=
        ((1:ℂ) ⊗ₜ[R] (Ideal.Quotient.mk V.affineIdeal P)) :=
      T.symm_apply_eq.mpr (projectivePulledCutEquationTensorFiberEquiv_tmul f V L w P).symm
    rw [hP]
/-- Complete ORIGINAL Setup DERIVES the actual cut-coefficient fiber duality
on one nonempty original parameter open. Every original polynomial value,
literal eval1 trace and source-action square are preserved. No extra
generic-freeness input;FIXED normalization and SAME top-H remain OPEN. -/
theorem projectivePulledCutEquation_originalSetup_exists_coefficient_dual_open {n r : ℕ}
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
        projectivePulledCutEquationCoefficientFiberDualStatement f V L w := by
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
  exact ⟨hfiniteA w hwa,projectivePulledCutEquation_coefficient_fiber_dual_of_smooth_cut f V
    (chosenProjectiveNormalization_definingIdeal_ne_bot V L hinj hfinite hrn) L w
    (chosenProjectiveNormalization_chart_dimension V L hinj hfinite x0 hx0)
    (hfiniteA w hwa) hsmooth⟩
end LinearStudy
