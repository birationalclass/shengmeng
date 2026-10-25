module
public import Linear.OriginalCutEquationCoefficientFiberDual
public import Linear.CoextensionOriginalCoefficientQuotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- Actual original cut-coefficient QUOTIENT duality. Statement definition,
not a proof. The quotient ideal is the SAME original H ideal;the source
is the native coextension with its ORIGINAL upper-ring action. -/
def projectivePulledCutEquationCoefficientQuotientDualStatement {n r : ℕ}
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
    let D := (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)
    letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
    let I := Ideal.span (Set.range (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))
    ∃ F : (D ⧸ (I • (⊤ : Submodule B D))) ≃ₗ[ℂ] Module.Dual ℂ Q,
      (∀ (ell : D) (P : MvPolynomial (Fin n) ℂ),
        F (Submodule.Quotient.mk ell) (Ideal.Quotient.mk J P)=
          algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
            (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
              (Ideal.Quotient.mk V.affineIdeal P))) ∧
      (∀ (ell : D),F (Submodule.Quotient.mk ell) 1=
        algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1)) ∧
      (∀ (P : MvPolynomial (Fin n) ℂ) z q,
        F ((Ideal.Quotient.mk V.affineIdeal P) • z) q=
          F z (q*Ideal.Quotient.mk J P))
/-- Join the actual native coefficient quotient to the SAME original cut
ring dual,retaining EVERY original coefficient value,literal evaluation
at1,and ORIGINAL source multiplication. No source action is transported. -/
theorem projectivePulledCutEquation_coefficient_quotient_dual_of_fiber_dual {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hdual : projectivePulledCutEquationCoefficientFiberDualStatement f V L w) :
    projectivePulledCutEquationCoefficientQuotientDualStatement f V L w := by
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
  let D := (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)
  letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
  have hres : Function.Surjective (algebraMap R ℂ) :=
    fun a => ⟨MvPolynomial.C a,rho.commutes a⟩
  let I := Ideal.span (Set.range (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
    (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))
  let m := RingHom.ker (algebraMap R ℂ)
  have hI : m.map (algebraMap R B)=I :=
    projectivePulledCutEquationMap_zero_fiber_ideal f V L w
  let Qe := (Submodule.quotEquivOfEq (I • (⊤ : Submodule B D))
    (m.map (algebraMap R B) • (⊤ : Submodule B D))
      (congrArg (fun T : Ideal B => T • (⊤ : Submodule B D)) hI.symm)).restrictScalars ℂ
  let E0 := coextensionOriginalCoefficientQuotientFiberEquiv (K:=ℂ) (R:=R) (S:=B) hres
  unfold projectivePulledCutEquationCoefficientFiberDualStatement at hdual
  dsimp only at hdual
  obtain ⟨E,hpure,hunit,hscalar⟩ := hdual
  unfold projectivePulledCutEquationCoefficientQuotientDualStatement
  dsimp only
  refine ⟨Qe.trans (E0.trans E),?_,?_,?_⟩
  · intro ell P
    change E (E0 (Submodule.Quotient.mk ell)) (Ideal.Quotient.mk _ P)=_
    rw [coextensionOriginalCoefficientQuotientFiberEquiv_mk]
    simpa only [one_mul] using hpure (1:ℂ) ell P
  · intro ell
    change E (E0 (Submodule.Quotient.mk ell)) 1=_
    rw [coextensionOriginalCoefficientQuotientFiberEquiv_mk]
    simpa only [one_mul,map_one] using hpure (1:ℂ) ell (1 : MvPolynomial (Fin n) ℂ)
  · intro P z q
    induction z using Submodule.Quotient.induction_on with
    | _ ell =>
      change E (E0 (Submodule.Quotient.mk ((Ideal.Quotient.mk V.affineIdeal P) • ell))) q=
        E (E0 (Submodule.Quotient.mk ell)) (q*Ideal.Quotient.mk _ P)
      rw [coextensionOriginalCoefficientQuotientFiberEquiv_mk,
        coextensionOriginalCoefficientQuotientFiberEquiv_mk]
      change E (coextensionOriginalScalarFiberEnd (R:=R) (K:=ℂ)
        (Ideal.Quotient.mk V.affineIdeal P) ((1:ℂ) ⊗ₜ[R] ell)) q=_
      exact hscalar P ((1:ℂ) ⊗ₜ[R] ell) q
/-- Complete ORIGINAL Setup DERIVES quotient duality for the SAME H ideal
on the SAME nonempty original open. No quotient comparison or freeness
certificate is a hypothesis. FIXED normalization/top-H remain OPEN. -/
theorem projectivePulledCutEquation_originalSetup_exists_coefficient_quotient_dual_open {n r : ℕ}
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
        projectivePulledCutEquationCoefficientQuotientDualStatement f V L w := by
  obtain ⟨c,hc,hex,hcprop⟩ := projectivePulledCutEquation_originalSetup_exists_coefficient_dual_open
    f V hrn hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  exact ⟨(hcprop w hw).1,projectivePulledCutEquation_coefficient_quotient_dual_of_fiber_dual
    f V L w (hcprop w hw).2⟩
end LinearStudy
