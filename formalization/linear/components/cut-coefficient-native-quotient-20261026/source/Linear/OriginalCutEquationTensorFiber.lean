module
public import Linear.ProjectiveCutEquationMapFinite
public import Linear.SurjectiveBaseFiberQuotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open TensorProduct
/-- For the NAMED actual original equation map,the actual zero-fiber
ideal is literally the SAME original equation ideal. -/
theorem projectivePulledCutEquationMap_zero_fiber_ideal {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    (RingHom.ker (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom).map
      (projectivePulledCutEquationMap f V L w).toRingHom=
    Ideal.span (Set.range (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))) := by
  have he : projectivePulledCutEquationMap f V L w=
      MvPolynomial.aeval (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))) := by
    dsimp only [projectivePulledCutEquationMap]
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using
      (MvPolynomial.comp_aeval (f:=fun i : Fin r => affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal))
  rw [he]
  exact polynomial_equation_zero_fiber_ideal _
/-- The ACTUAL original equation-map tensor fiber is the SAME original
cut ring as an algebra over the ORIGINAL field. No point-set substitution,
radical,freeness or comparison-iso hypothesis. -/
def projectivePulledCutEquationTensorFiberEquiv {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    let R := MvPolynomial (Fin r) ℂ
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let phi := projectivePulledCutEquationMap f V L w
    letI : Algebra R B := phi.toRingHom.toAlgebra
    letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
    letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
    letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom.toAlgebra
    ℂ ⊗[R] B ≃ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom) := by
  dsimp only
  let R := MvPolynomial (Fin r) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let phi := projectivePulledCutEquationMap f V L w
  let rho : R →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin r → ℂ)
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  letI : Algebra R ℂ := rho.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R B := IsScalarTower.of_algHom phi
  letI : IsScalarTower ℂ R ℂ := IsScalarTower.of_algHom rho
  have hres : Function.Surjective (algebraMap R ℂ) :=
    fun a => ⟨MvPolynomial.C a,rho.commutes a⟩
  let E := surjectiveBaseFiberQuotientOriginalFieldEquiv (S:=B) hres
  let hI := projectivePulledCutEquationMap_zero_fiber_ideal f V L w
  exact E.symm.trans ((Ideal.quotientEquivAlgOfEq ℂ hI).trans
    (projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w))
/-- The constructed tensor-fiber comparison preserves EVERY original
polynomial class,not merely the support or an unspecified algebra iso. -/
theorem projectivePulledCutEquationTensorFiberEquiv_tmul {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (a : MvPolynomial (Fin n) ℂ) :
    let R := MvPolynomial (Fin r) ℂ
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let phi := projectivePulledCutEquationMap f V L w
    letI : Algebra R B := phi.toRingHom.toAlgebra
    letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
    letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
    letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom.toAlgebra
    projectivePulledCutEquationTensorFiberEquiv f V L w
      ((1:ℂ) ⊗ₜ[R] (Ideal.Quotient.mk V.affineIdeal a))=Ideal.Quotient.mk _ a := by
  dsimp only
  let R := MvPolynomial (Fin r) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let phi := projectivePulledCutEquationMap f V L w
  let rho : R →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin r → ℂ)
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  letI : Algebra R ℂ := rho.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R B := IsScalarTower.of_algHom phi
  letI : IsScalarTower ℂ R ℂ := IsScalarTower.of_algHom rho
  have hres : Function.Surjective (algebraMap R ℂ) :=
    fun a => ⟨MvPolynomial.C a,rho.commutes a⟩
  let E := surjectiveBaseFiberQuotientOriginalFieldEquiv (S:=B) hres
  have hE : E.symm ((1:ℂ) ⊗ₜ[R] (Ideal.Quotient.mk V.affineIdeal a))=
      Ideal.Quotient.mk _ (Ideal.Quotient.mk V.affineIdeal a) :=
    E.symm_apply_eq.mpr (surjectiveBaseFiberQuotientOriginalFieldEquiv_mk
      hres (Ideal.Quotient.mk V.affineIdeal a)).symm
  change projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w
    (Ideal.quotientEquivAlgOfEq ℂ (projectivePulledCutEquationMap_zero_fiber_ideal f V L w)
      (E.symm ((1:ℂ) ⊗ₜ[R] (Ideal.Quotient.mk V.affineIdeal a))))=_
  rw [hE]
  change projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk V.affineIdeal a))=_
  exact projectivePulledLinearSection_koszulQuotientAlgEquiv_mk f V L w a
end LinearStudy
