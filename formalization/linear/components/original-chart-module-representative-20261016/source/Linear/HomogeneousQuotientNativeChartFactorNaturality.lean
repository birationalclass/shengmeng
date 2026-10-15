module
public import Linear.HomogeneousQuotientNativeCutChartMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading
variable {K : Type*} [Field K] {n : ℕ}

/-- Full original homogeneous-fraction formulas force the ACTUAL native
chart ring isomorphisms to intertwine the ORIGINAL quotient factor map.
The two fraction formulas are explicit inputs of this generic bridge. -/
theorem homogeneousQuotient_nativeChart_factor_of_fraction_formulas
    (I J : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K)) (hIJ : I ≤ J) :
    letI := homogeneousQuotientGrading I hI
    letI := homogeneousQuotientGrading J hJ
    ∀ (eI : (MvPolynomial (Fin n) K ⧸ I.map (affineChartPolynomialMap (K := K)).toRingHom) ≃+*
        Away (homogeneousQuotientPiece I) (Ideal.Quotient.mk I (MvPolynomial.X 0))),
      (∀ (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m),
        eI (Ideal.Quotient.mk _ (affineChartPolynomialMap H)) =
          homogeneousQuotientNativeChartElement I hI m H hH) →
    ∀ (eJ : (MvPolynomial (Fin n) K ⧸ J.map (affineChartPolynomialMap (K := K)).toRingHom) ≃+*
        Away (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0))),
      (∀ (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m),
        eJ (Ideal.Quotient.mk _ (affineChartPolynomialMap H)) =
          homogeneousQuotientNativeChartElement J hJ m H hH) →
    ∀ x, Away.map (homogeneousQuotientFactorGraded I J hIJ)
      (Ideal.Quotient.mk I (MvPolynomial.X 0)) (eI x) =
        eJ (Ideal.Quotient.factor (Ideal.map_mono hIJ) x) := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientGrading J hJ
  intro eI heI eJ heJ x
  let F : MvPolynomial (Fin n) K →+*
      Away (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0)) := (Away.map (homogeneousQuotientFactorGraded I J hIJ)
      (Ideal.Quotient.mk I (MvPolynomial.X 0))).comp
    (eI.toRingHom.comp (Ideal.Quotient.mk (I.map (affineChartPolynomialMap (K := K)).toRingHom)))
  let G : MvPolynomial (Fin n) K →+*
      Away (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0)) := eJ.toRingHom.comp (Ideal.Quotient.mk (J.map (affineChartPolynomialMap (K := K)).toRingHom))
  have hh (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m) :
      F (affineChartPolynomialMap H) = G (affineChartPolynomialMap H) := by
    change Away.map (homogeneousQuotientFactorGraded I J hIJ)
      (Ideal.Quotient.mk I (MvPolynomial.X 0))
      (eI (Ideal.Quotient.mk _ (affineChartPolynomialMap H))) =
        eJ (Ideal.Quotient.mk _ (affineChartPolynomialMap H))
    rw [heI m H hH,heJ m H hH]
    exact homogeneousQuotientFactor_away_originalFraction I J hI hJ hIJ m H hH
  have hFG : F = G := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [affineChartPolynomialMap,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq] using
        hh 0 (MvPolynomial.C c) (MvPolynomial.isHomogeneous_C (Fin (n+1)) c)
    · intro t
      simpa only [affineChartPolynomialMap,MvPolynomial.aeval_X,Fin.cases_succ] using
        hh 1 (MvPolynomial.X t.succ) (MvPolynomial.isHomogeneous_X K t.succ)
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun hFG p

/-- Construct BOTH actual native chart ring isomorphisms from the
already PROVED original fraction theorem,and DERIVE original quotient-map
compatibility. Neither the maps nor their desired naturality is assumed. -/
theorem homogeneousQuotient_nativeChart_exists_factor_compatible
    (I J : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K)) (hIJ : I ≤ J) :
    letI := homogeneousQuotientGrading I hI
    letI := homogeneousQuotientGrading J hJ
    ∃ (eI : (MvPolynomial (Fin n) K ⧸ I.map (affineChartPolynomialMap (K := K)).toRingHom) ≃+*
        Away (homogeneousQuotientPiece I) (Ideal.Quotient.mk I (MvPolynomial.X 0))),
    ∃ (eJ : (MvPolynomial (Fin n) K ⧸ J.map (affineChartPolynomialMap (K := K)).toRingHom) ≃+*
        Away (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0))),
      (∀ (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m),
        eI (Ideal.Quotient.mk _ (affineChartPolynomialMap H)) =
          homogeneousQuotientNativeChartElement I hI m H hH) ∧
      (∀ (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m),
        eJ (Ideal.Quotient.mk _ (affineChartPolynomialMap H)) =
          homogeneousQuotientNativeChartElement J hJ m H hH) ∧
      ∀ x, Away.map (homogeneousQuotientFactorGraded I J hIJ)
        (Ideal.Quotient.mk I (MvPolynomial.X 0)) (eI x) =
          eJ (Ideal.Quotient.factor (Ideal.map_mono hIJ) x) := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientGrading J hJ
  obtain ⟨eI,heI⟩ := homogeneousQuotient_nativeChart_ringEquiv I hI
  obtain ⟨eJ,heJ⟩ := homogeneousQuotient_nativeChart_ringEquiv J hJ
  refine ⟨eI,eJ,heI,heJ,?_⟩
  exact homogeneousQuotient_nativeChart_factor_of_fraction_formulas I J hI hJ hIJ eI heI eJ heJ

end LinearStudy
