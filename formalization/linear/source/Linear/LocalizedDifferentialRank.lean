module
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Linear.SmoothCotangentDimension
public import Linear.SmoothCommonFormalCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open scoped Matrix
attribute [local instance] polynomialLocalDifferentialModule

/-- Localization preserves the actual differential-module rank over a domain.
No global smoothness or global flatness hypothesis is imposed. -/
theorem localized_differential_finrank
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B] [IsDomain A]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (M : Submonoid A) [IsLocalization M B] (hM : M ≤ nonZeroDivisors A) :
    Module.finrank B (KaehlerDifferential K B) =
      Module.finrank A (KaehlerDifferential K A) := by
  rw [IsLocalization.finrank_eq B M hM]
  exact IsLocalizedModule.finrank_eq M (KaehlerDifferential.map K K A B) hM

theorem atPrime_differential_finrank
    {K A : Type*} [CommRing K] [CommRing A] [IsDomain A] [Algebra K A]
    (P : Ideal A) [P.IsPrime] :
    Module.finrank (Localization.AtPrime P)
      (KaehlerDifferential K (Localization.AtPrime P)) =
      Module.finrank A (KaehlerDifferential K A) := by
  exact localized_differential_finrank P.primeCompl P.primeCompl_le_nonZeroDivisors

theorem atPrime_differential_finrank_eq
    {K A : Type*} [CommRing K] [CommRing A] [IsDomain A] [Algebra K A]
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] :
    Module.finrank (Localization.AtPrime P)
      (KaehlerDifferential K (Localization.AtPrime P)) =
    Module.finrank (Localization.AtPrime Q)
      (KaehlerDifferential K (Localization.AtPrime Q)) := by
  rw [atPrime_differential_finrank P, atPrime_differential_finrank Q]

/-- The rank comparison for the original embedded localized ideal quotient,
rather than a supplied local-coordinate model. -/
theorem polynomial_local_differential_finrank
    {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [I.IsPrime] [P.IsPrime] (hIP : I ≤ P) :
    let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
    Module.finrank Q (KaehlerDifferential K Q) =
      Module.finrank (MvPolynomial σ K ⧸ I)
        (KaehlerDifferential K (MvPolynomial σ K ⧸ I)) := by
  intro Q
  let A := MvPolynomial σ K ⧸ I
  let M := Algebra.algebraMapSubmonoid A P.primeCompl
  let : IsScalarTower K A Q := IsScalarTower.of_algebraMap_eq (R := K) (S := A) (A := Q) (fun k => by
    change Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
      (algebraMap K (Localization.AtPrime P) k) = _
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial σ K) (Localization.AtPrime P)]
    rfl)
  have hM : M ≤ nonZeroDivisors A := by
    rintro z ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    exact ha (hIP (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
  exact localized_differential_finrank M hM

theorem smooth_polynomial_conormal_finrank
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [I.IsPrime] [P.IsPrime] (hIP : I ≤ P)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
    Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent =
      Nat.card σ - Module.finrank (MvPolynomial σ K ⧸ I)
        (KaehlerDifferential K (MvPolynomial σ K ⧸ I)) := by
  intro Q
  have h := smooth_polynomial_cotangent_finrank_add I P hIP
  change Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent +
    Module.finrank Q (KaehlerDifferential K Q) = Nat.card σ at h
  rw [polynomial_local_differential_finrank I P hIP] at h
  change Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent = _
  omega

theorem smooth_prime_polynomial_conormal_rank_positive
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [I.IsPrime] [P.IsPrime]
    (hI : I ≠ ⊥) (hIP : I ≤ P)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    0 < Nat.card σ - Module.finrank (MvPolynomial σ K ⧸ I)
      (KaehlerDifferential K (MvPolynomial σ K ⧸ I)) := by
  let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I P hIP)
  obtain ⟨n, G, hG, b, hb, hs⟩ := exists_smooth_polynomial_local_generators I P hIP
  have hn : Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent = n := by
    simpa using Module.finrank_eq_card_basis b
  have hpos : 0 < n := by
    have hloc : I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hI
    cases n with
    | zero =>
      exfalso
      apply hloc
      simpa using hs
    | succ n => exact Nat.succ_pos n
  rw [← smooth_polynomial_conormal_finrank I P hIP, hn]
  exact hpos

/-- Smooth rational points on a single nonzero prime embedded variety admit
one actual ambient change and normal-ideal presentation. Common conormal rank
and normal-coordinate columns are derived, rather than supplied. -/
theorem smooth_prime_points_have_common_formal_normal_coordinates
    {K σ ι : Type*} [Field K] [Infinite K] [Fintype σ] [DecidableEq σ]
    [Fintype ι] [Nonempty ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (hI : I ≠ ⊥)
    (P : ι → Ideal (MvPolynomial σ K)) [∀ a, (P a).IsPrime]
    (x : ι → σ → K) (hIP : ∀ a, I ≤ P a)
    (hP : ∀ a, P a = RingHom.ker (MvPolynomial.aeval (R := K) (x a)).toRingHom)
    [∀ a, Algebra.FormallySmooth K
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a))))] :
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
  classical
  let c := Nat.card σ - Module.finrank (MvPolynomial σ K ⧸ I)
    (KaehlerDifferential K (MvPolynomial σ K ⧸ I))
  let a := Classical.arbitrary ι
  have hc : 0 < c := smooth_prime_polynomial_conormal_rank_positive I (P a) hI (hIP a)
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  have hcle : Fintype.card (Fin c) ≤ Fintype.card σ := by
    simp only [Fintype.card_fin]
    exact (Nat.sub_le _ _).trans_eq (Nat.card_eq_fintype_card (α := σ))
  obtain ⟨ν⟩ := Function.Embedding.nonempty_of_card_le hcle
  have hrank : ∀ a, Module.finrank
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a))))
      (polynomialLocalQuotientExtension I (P a)).Cotangent = c :=
    fun a => smooth_polynomial_conormal_finrank I (P a) (hIP a)
  obtain ⟨r, e, M, hM, G, h⟩ :=
    smooth_points_have_common_formal_normal_coordinates I P x hIP hP ν ν.injective hrank
  exact ⟨r, c, hc, e, M, hM, G, h⟩

end LinearStudy
