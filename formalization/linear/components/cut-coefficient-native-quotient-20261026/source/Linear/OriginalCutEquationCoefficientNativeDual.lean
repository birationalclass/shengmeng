module
public import Linear.OriginalCutEquationCoefficientQuotientDual
public import Linear.FieldDualNativeCoextensionSource
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
/-- The ACTUAL quotient map from the ORIGINAL affine variety ring to
SAME ORIGINAL cut ring,using the already constructed Koszul quotient. -/
def projectivePulledCutOriginalRingMap {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ]
      (MvPolynomial (Fin n) ℂ ⧸ (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K:=ℂ)).toRingHom) :=
  (projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w).toAlgHom.comp
    (Ideal.Quotient.mkₐ ℂ _)
/-- The actual cut map retains EVERY ORIGINAL polynomial class. -/
theorem projectivePulledCutOriginalRingMap_mk {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    projectivePulledCutOriginalRingMap f V L w (Ideal.Quotient.mk V.affineIdeal P)=
      Ideal.Quotient.mk _ P :=
  projectivePulledLinearSection_koszulQuotientAlgEquiv_mk f V L w P
/-- The original cut map is an ACTUAL surjective ring map. -/
theorem projectivePulledCutOriginalRingMap_surjective {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    Function.Surjective (projectivePulledCutOriginalRingMap f V L w) := by
  intro q
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk V.affineIdeal P,
    projectivePulledCutOriginalRingMap_mk f V L w P⟩
/-- Actual ORIGINAL B-linear quotient duality into the native coextension
on SAME cut Q,restricted through ACTUAL original cut map. Statement only,
not a proof. Original values and eval1 are retained explicitly. -/
def projectivePulledCutEquationCoefficientNativeDualStatement {n r : ℕ}
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
    ∃ F : (D ⧸ (I • (⊤ : Submodule B D))) ≃ₗ[B]
        (ModuleCat.restrictScalars (projectivePulledCutOriginalRingMap f V L w).toRingHom).obj Dq,
      (∀ (ell : D) (P : MvPolynomial (Fin n) ℂ),
        (show Dq from F (Submodule.Quotient.mk ell)) (Ideal.Quotient.mk J P)=
          algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
            (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
              (Ideal.Quotient.mk V.affineIdeal P))) ∧
      (∀ (ell : D),(show Dq from F (Submodule.Quotient.mk ell)) (1:Q)=
        algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1))
/-- Original quotient-source action compatibility DERIVES an ACTUAL
B-linear equivalence to the native cut dual,not a transported action. -/
theorem projectivePulledCutEquation_native_dual_of_quotient_dual {n r : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hdual : projectivePulledCutEquationCoefficientQuotientDualStatement f V L w) :
    projectivePulledCutEquationCoefficientNativeDualStatement f V L w := by
  let R := MvPolynomial (Fin r) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let phi := projectivePulledCutEquationMap f V L w
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin r → ℂ)).toRingHom.toAlgebra
  let D := (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)
  letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
  let beta := projectivePulledCutOriginalRingMap f V L w
  unfold projectivePulledCutEquationCoefficientQuotientDualStatement at hdual
  dsimp only at hdual
  obtain ⟨F,hvalues,hunit,hscalar⟩ := hdual
  have hs : ∀ b z q,F (b • z) q=F z (q*beta b) := by
    intro b z q
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [projectivePulledCutOriginalRingMap_mk]
    exact hscalar P z q
  let Fnew := fieldDualNativeCoextensionSourceEquiv beta.toRingHom F hs
  unfold projectivePulledCutEquationCoefficientNativeDualStatement
  dsimp only
  refine ⟨Fnew,?_,?_⟩
  · intro ell P
    rw [fieldDualNativeCoextensionSourceEquiv_apply]
    exact hvalues ell P
  · intro ell
    rw [fieldDualNativeCoextensionSourceEquiv_apply]
    exact hunit ell
/-- Full ORIGINAL Setup DERIVES actual native B-linear cut-coefficient
duality on SAME nonempty open. No auxiliary iso or global free/flat/CM
input. Fixed original normalization and SAME top-H remain OPEN. -/
theorem projectivePulledCutEquation_originalSetup_exists_native_coefficient_dual_open {n r : ℕ}
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
        projectivePulledCutEquationCoefficientNativeDualStatement f V L w := by
  obtain ⟨c,hc,hex,hcprop⟩ := projectivePulledCutEquation_originalSetup_exists_coefficient_quotient_dual_open
    f V hrn hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  exact ⟨(hcprop w hw).1,projectivePulledCutEquation_native_dual_of_quotient_dual
    f V L w (hcprop w hw).2⟩
end LinearStudy
