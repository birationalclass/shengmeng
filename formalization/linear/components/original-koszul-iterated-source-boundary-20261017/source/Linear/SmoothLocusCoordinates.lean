module
public import Mathlib.RingTheory.Smooth.Locus
public import Linear.LocalFiber
public import Linear.LocalizedDifferentialRank
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open scoped Matrix

/-- Smoothness at an actual prime of the quotient transfers to the actual
ambient localization modulo the original ideal. -/
theorem quotient_smoothAt_formallySmooth_localized_ideal
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I : Ideal R) (p : Ideal (R ⧸ I)) [p.IsPrime] [Algebra.IsSmoothAt K p] :
    Algebra.FormallySmooth K
      (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap R (Localization.AtPrime (p.comap (Ideal.Quotient.mk I))))) := by
  let P := p.comap (Ideal.Quotient.mk I)
  let B := Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))
  let : IsScalarTower K (R ⧸ I) B :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := R ⧸ I) (A := B) (fun k => by
      change Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime P)))
        (algebraMap K (Localization.AtPrime P) k) = _
      rw [IsScalarTower.algebraMap_apply K R (Localization.AtPrime P)]
      rfl)
  exact Algebra.FormallySmooth.of_equiv
    ((localizationQuotientEquiv I p).restrictScalars K).symm

/-- Starting with the library's smooth points of the original prime quotient,
construct one ambient coordinate change and formal normal-ideal maps at all
selected rational points. -/
theorem smoothLocus_prime_points_have_common_formal_normal_coordinates
    {K σ ι : Type*} [Field K] [Infinite K] [Fintype σ] [DecidableEq σ]
    [Fintype ι] [Nonempty ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (hI : I ≠ ⊥)
    (p : ι → Ideal (MvPolynomial σ K ⧸ I)) [∀ a, (p a).IsPrime]
    [∀ a, Algebra.IsSmoothAt K (p a)]
    (x : ι → σ → K)
    (hp : ∀ a, (p a).comap (Ideal.Quotient.mk I) =
      RingHom.ker (MvPolynomial.aeval (R := K) (x a)).toRingHom) :
    ∃ (r c : ℕ) (hc : 0 < c),
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ σ)
        (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0)
        (G : ι → Fin c → MvPolynomial σ K),
        let C := polynomialLinearChangeEquiv M hM
        let y : ι → Fin r ⊕ Fin c → K := fun a => (M⁻¹ *ᵥ x a) ∘ e
        let H : ι → Fin c → MvPolynomial (Fin r ⊕ Fin c) K :=
          fun a i => MvPolynomial.rename e.symm (C (G a i))
        ∃ (hH : ∀ a i, MvPolynomial.eval (y a) (H a i) = 0)
          (hJ : ∀ a, IsUnit (Matrix.det (fun i j => MvPolynomial.eval (y a)
            (MvPolynomial.pderiv (Sum.inr j) (H a i))))),
          ∀ a, I.map (((polynomialSmoothFormalMap (y a) (H a) (hH a) (hJ a)).comp
            (MvPolynomial.rename e.symm).toRingHom).comp C.toRingHom) =
              Ideal.span (Set.range (MvPowerSeries.X
                (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  let P := fun a => (p a).comap (Ideal.Quotient.mk I)
  let : ∀ a, Algebra.FormallySmooth K
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a)))) :=
    fun a => quotient_smoothAt_formallySmooth_localized_ideal I (p a)
  have hIP : ∀ a, I ≤ P a := by
    intro a z hz
    change Ideal.Quotient.mk I z ∈ p a
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
    exact (p a).zero_mem
  exact smooth_prime_points_have_common_formal_normal_coordinates I hI P x hIP hp

end LinearStudy
