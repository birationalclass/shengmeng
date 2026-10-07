module
public import Linear.SmoothJacobianMinor
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace LinearStudy

theorem smooth_extension_cotangent_decomposition {K S : Type*}
    [CommRing K] [CommRing S] [Algebra K S]
    (E : Algebra.Extension K S) [Algebra.FormallySmooth K E.Ring]
    [Algebra.FormallySmooth K S] :
    Nonempty (E.CotangentSpace ≃ₗ[S] E.Cotangent × KaehlerDifferential K S) := by
  obtain ⟨l, hl⟩ := (Algebra.Extension.formallySmooth_iff_split_injection E).mp inferInstance
  exact ⟨((E.exact_cotangentComplex_toKaehler).splitInjectiveEquiv
    E.toKaehler_surjective ⟨l, hl⟩).val⟩

theorem smooth_extension_cotangent_finrank_add {K S σ : Type*}
    [CommRing K] [CommRing S] [Algebra K S] [IsLocalRing S] [Fintype σ]
    (E : Algebra.Extension K S) [Algebra.FormallySmooth K E.Ring]
    [Algebra.FormallySmooth K S] (hE : E.ker.FG)
    (b : Module.Basis σ S E.CotangentSpace) :
    Module.finrank S E.Cotangent + Module.finrank S (KaehlerDifferential K S) =
      Fintype.card σ := by
  let : Module.Finite S E.CotangentSpace := Module.Finite.of_basis b
  let : Module.Finite S E.Cotangent := Algebra.Extension.Cotangent.finite (P := E) hE
  let : Module.Free S E.Cotangent := extension_cotangent_free_of_formallySmooth E hE
  let : Module.Finite S (KaehlerDifferential K S) :=
    Module.Finite.of_surjective E.toKaehler E.toKaehler_surjective
  let : Module.Free S (KaehlerDifferential K S) := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := smooth_extension_cotangent_decomposition E
  rw [← Module.finrank_prod, ← e.finrank_eq, Module.finrank_eq_card_basis b]

theorem polynomial_local_ideal_ne_top {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) :
    I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊤ := by
  have hle : I.map (algebraMap _ (Localization.AtPrime P)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIP
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle

/- Explicitly select the standard scalar ring for the library's differential
module instance; no additional mathematical hypothesis is introduced. -/
@[instance_reducible] def polynomialLocalDifferentialModule {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    Module (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (KaehlerDifferential K
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))) := by
  let S := Localization.AtPrime P
  let J : Ideal S := I.map (algebraMap _ S)
  change Module (S ⧸ J) (KaehlerDifferential K (S ⧸ J))
  exact instModuleKaehlerDifferentialOfSMulCommClass K (S ⧸ J) (R' := S ⧸ J)

attribute [local instance] polynomialLocalDifferentialModule

theorem smooth_polynomial_cotangent_finrank_add {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
    Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent +
      Module.finrank Q (KaehlerDifferential K Q) = Nat.card σ := by
  intro Q
  let E := polynomialLocalQuotientExtension I P
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (polynomial_local_ideal_ne_top I P hIP)
  let : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing E.Ring := inferInstanceAs (IsNoetherianRing (Localization.AtPrime P))
  let : Algebra.FormallySmooth K E.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K (Localization.AtPrime P))
  let := Fintype.ofFinite σ
  simpa only [Nat.card_eq_fintype_card] using
    smooth_extension_cotangent_finrank_add E (IsNoetherian.noetherian E.ker)
      (polynomialLocalCotangentSpaceBasis I P)

theorem smooth_polynomial_split_tangent_finrank {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))]
    {r c : ℕ} (e : (Fin r ⊕ Fin c) ≃ σ)
    (b : Module.Basis (Fin c)
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (polynomialLocalQuotientExtension I P).Cotangent) :
    Module.finrank (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (KaehlerDifferential K
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))) = r := by
  let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (polynomial_local_ideal_ne_top I P hIP)
  have hb : Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent = c := by
    simpa using Module.finrank_eq_card_basis b
  have ha := smooth_polynomial_cotangent_finrank_add I P hIP
  change Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent +
    Module.finrank Q (KaehlerDifferential K Q) = Nat.card σ at ha
  have he : r + c = Nat.card σ := by
    rw [← Nat.card_congr e]
    simp
  rw [hb] at ha
  change Module.finrank Q (KaehlerDifferential K Q) = r
  omega

end LinearStudy
