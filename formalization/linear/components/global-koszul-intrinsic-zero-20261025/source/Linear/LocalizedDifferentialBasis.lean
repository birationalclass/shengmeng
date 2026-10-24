module
public import Linear.SmoothPolynomialGenerators
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Basis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy

/-- The actual differential basis on the localized polynomial ambient ring. -/
def polynomialLocalizedDifferentialBasis {K σ : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    Module.Basis σ (Localization.AtPrime P)
      (KaehlerDifferential K (Localization.AtPrime P)) :=
  ((KaehlerDifferential.mvPolynomialBasis K σ).baseChange (Localization.AtPrime P)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      K (MvPolynomial σ K) (Localization.AtPrime P))

theorem polynomialLocalizedDifferentialBasis_apply {K σ : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (i : σ) :
    polynomialLocalizedDifferentialBasis P i =
      KaehlerDifferential.D K (Localization.AtPrime P)
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (MvPolynomial.X i)) := by
  simp [polynomialLocalizedDifferentialBasis, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D]
  exact one_smul (Localization.AtPrime P)
    (KaehlerDifferential.D K (Localization.AtPrime P)
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (MvPolynomial.X i)))

theorem polynomialLocalizedDifferentialBasis_repr_D {K σ : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (G : MvPolynomial σ K) (i : σ) :
    (polynomialLocalizedDifferentialBasis P).repr
      (KaehlerDifferential.D K (Localization.AtPrime P)
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) G)) i =
      algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (MvPolynomial.pderiv i G) := by
  change ((KaehlerDifferential.mvPolynomialBasis K σ).baseChange (Localization.AtPrime P)).repr
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      K (MvPolynomial σ K) (Localization.AtPrime P)).symm
      (KaehlerDifferential.D K (Localization.AtPrime P)
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) G))) i = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul, KaehlerDifferential.mvPolynomialBasis_repr_apply]
  simp [Algebra.smul_def]

theorem polynomialLocalizedDifferentialBasis_baseChange_repr_D
    {K σ Q : Type*} [Field K] [CommRing Q]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] [Algebra (Localization.AtPrime P) Q]
    (G : MvPolynomial σ K) (i : σ) :
    ((polynomialLocalizedDifferentialBasis P).baseChange Q).repr
      (1 ⊗ₜ[Localization.AtPrime P]
        KaehlerDifferential.D K (Localization.AtPrime P)
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) G)) i =
      algebraMap (Localization.AtPrime P) Q
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (MvPolynomial.pderiv i G)) := by
  rw [Module.Basis.baseChange_repr_tmul, polynomialLocalizedDifferentialBasis_repr_D]
  simp [Algebra.smul_def]

end LinearStudy
