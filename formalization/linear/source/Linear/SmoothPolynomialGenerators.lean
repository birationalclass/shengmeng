module
public import Linear.SmoothConormal
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

def polynomialLocalQuotientExtension {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    Algebra.Extension K (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) :=
  Algebra.Extension.ofSurjective
    (Ideal.Quotient.mkₐ K (I.map (algebraMap _ (Localization.AtPrime P))))
    Ideal.Quotient.mk_surjective

theorem polynomialLocalQuotientExtension_ker {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    (polynomialLocalQuotientExtension I P).ker = I.map (algebraMap _ (Localization.AtPrime P)) := by
  change RingHom.ker (Ideal.Quotient.mk _) = _
  exact Ideal.mk_ker

theorem exists_smooth_polynomial_local_generators {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    let E := polynomialLocalQuotientExtension I P
    ∃ (n : ℕ) (G : Fin n → MvPolynomial σ K)
      (hG : ∀ i, algebraMap _ (Localization.AtPrime P) (G i) ∈ E.ker)
      (b : Module.Basis (Fin n)
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) E.Cotangent),
      (∀ i, Algebra.Extension.Cotangent.mk ⟨algebraMap _ (Localization.AtPrime P) (G i), hG i⟩ = b i) ∧
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))) := by
  intro E
  let S := Localization.AtPrime P
  let Q := S ⧸ I.map (algebraMap _ S)
  have hker : E.ker ≠ ⊤ := by
    rw [polynomialLocalQuotientExtension_ker]
    have hle : I.map (algebraMap _ S) ≤ IsLocalRing.maximalIdeal S := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hIP
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (by simpa only [E, polynomialLocalQuotientExtension_ker] using hker)
  let : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (I.map (algebraMap _ S))) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing E.Ring := inferInstanceAs (IsNoetherianRing S)
  let : IsLocalRing E.Ring := inferInstanceAs (IsLocalRing S)
  let : Algebra.FormallySmooth K E.Ring := inferInstanceAs (Algebra.FormallySmooth K S)
  let : IsScalarTower S Q E.Cotangent :=
    inferInstanceAs (IsScalarTower E.Ring Q E.Cotangent)
  obtain ⟨n, b, T, hT, hspan⟩ := exists_local_extension_generators_of_formallySmooth E hker
  let Tv : Fin n → S := fun i => (T i).val
  choose a ha using fun i => IsLocalization.surj (S := S) P.primeCompl (Tv i)
  let G := fun i => (a i).1
  let u : Fin n → Sˣ := fun i => (IsLocalization.map_units S (a i).2).unit
  have hu : ∀ i, (u i : S) = algebraMap (MvPolynomial σ K) S (a i).2 :=
    fun i => IsUnit.unit_spec _
  have hG : ∀ i, algebraMap (MvPolynomial σ K) S (G i) ∈ E.ker := by
    intro i
    rw [← ha i]
    exact E.ker.mul_mem_right _ (T i).property
  let uq : Fin n → Qˣ := fun i => Units.map (algebraMap S Q).toMonoidHom (u i)
  let b' := b.unitsSMul uq
  refine ⟨n, G, hG, b', ?_, ?_⟩
  · intro i
    have hi : (⟨algebraMap (MvPolynomial σ K) S (G i), hG i⟩ : E.ker) =
        (u i : S) • T i := by
      apply Subtype.ext
      change algebraMap (MvPolynomial σ K) S (G i) = (u i : S) * Tv i
      rw [hu, mul_comm]
      exact (ha i).symm
    rw [hi, map_smul, hT]
    change (u i : S) • b i = b.unitsSMul uq i
    rw [Module.Basis.unitsSMul_apply]
    exact (algebraMap_smul Q (u i : S) (b i)).symm
  · have hs : Ideal.span (Set.range Tv) = I.map (algebraMap _ S) :=
      hspan.trans (polynomialLocalQuotientExtension_ker I P)
    rw [← hs, ← span_unit_scaled_family Tv u]
    congr 2
    funext i
    rw [hu, mul_comm]
    exact ha i

end LinearStudy
