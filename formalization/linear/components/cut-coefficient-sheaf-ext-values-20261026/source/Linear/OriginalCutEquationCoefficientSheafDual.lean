module
public import Linear.OriginalCutEquationCoefficientNativeDual
public import Linear.TildePushforwardMappedUnitValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- ACTUAL original coefficient quotient sheaf is isomorphic to the ACTUAL
pushforward of the native dual on SAME original cut. Every original global
coefficient/polynomial value and literal eval1 must agree. Statement only,
not a proof. FIXED normalization and SAME geometric top-H remain OPEN. -/
def projectivePulledCutEquationCoefficientSheafDualStatement {n r : ℕ}
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
    let Dq := (ModuleCat.coextendScalars (algebraMap ℂ Q)).obj (ModuleCat.of ℂ ℂ)
    let I := Ideal.span (Set.range (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))
    let Bc := CommRingCat.of B
    let Qc := CommRingCat.of Q
    let beta : Bc ⟶ Qc := CommRingCat.ofHom (projectivePulledCutOriginalRingMap f V L w).toRingHom
    let M : ModuleCat Bc := ModuleCat.of B (D ⧸ (I • (⊤ : Submodule B D)))
    ∃ e : tilde M ≅ (Scheme.Modules.pushforward (Spec.map beta)).obj (tilde Dq),
      (∀ (ell : D) (P : MvPolynomial (Fin n) ℂ),
        (show Dq from tildePushforwardOriginalGlobalValue beta Dq M e
          (Submodule.Quotient.mk (p:=I • (⊤ : Submodule B D)) ell))
          (Ideal.Quotient.mk J P)=
            algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
              (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
                (Ideal.Quotient.mk V.affineIdeal P))) ∧
      (∀ (ell : D),
        (show Dq from tildePushforwardOriginalGlobalValue beta Dq M e
          (Submodule.Quotient.mk (p:=I • (⊤ : Submodule B D)) ell)) (1:Q)=
          algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
            (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1))
/-- ACTUAL B-linear native coefficient duality DERIVES the actual sheaf
isomorphism and its original-value/global-section square. The comparison
map is the mapped original module iso followed by actual tilde pushforward. -/
theorem projectivePulledCutEquation_sheaf_dual_of_native_dual {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hdual : projectivePulledCutEquationCoefficientNativeDualStatement f V L w) :
    projectivePulledCutEquationCoefficientSheafDualStatement f V L w := by
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
  let Dq := (ModuleCat.coextendScalars (algebraMap ℂ Q)).obj (ModuleCat.of ℂ ℂ)
  let I := Ideal.span (Set.range (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
    (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))
  let Bc := CommRingCat.of B
  let Qc := CommRingCat.of Q
  let beta : Bc ⟶ Qc := CommRingCat.ofHom (projectivePulledCutOriginalRingMap f V L w).toRingHom
  let M : ModuleCat Bc := ModuleCat.of B (D ⧸ (I • (⊤ : Submodule B D)))
  exact tildePushforward_existsOriginalTwoValues beta Dq M D
    (MvPolynomial (Fin n) ℂ)
    (fun ell => Submodule.Quotient.mk (p:=I • (⊤ : Submodule B D)) ell)
    (fun ell P z => (show Dq from z) (Ideal.Quotient.mk J P)=
      algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
        (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
          (Ideal.Quotient.mk V.affineIdeal P)))
    (fun ell z => (show Dq from z) (1:Q)=algebraMap R ℂ
      ((coextensionOriginalDualEquiv (R:=R) (S:=B)
        (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1)) hdual
/-- Full ORIGINAL Setup DERIVES actual native cut-dual sheaf comparison
on SAME original open,including every original coefficient value and
literal eval1 square. No comparison iso or global free/flat/CM input. -/
theorem projectivePulledCutEquation_originalSetup_exists_coefficient_sheaf_dual_open {n r : ℕ}
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
        projectivePulledCutEquationCoefficientSheafDualStatement f V L w := by
  obtain ⟨c,hc,hex,hcprop⟩ := projectivePulledCutEquation_originalSetup_exists_native_coefficient_dual_open
    f V hrn hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  exact ⟨(hcprop w hw).1,projectivePulledCutEquation_sheaf_dual_of_native_dual
    f V L w (hcprop w hw).2⟩
end LinearStudy
