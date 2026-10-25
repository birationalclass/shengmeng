module
public import Linear.PolynomialPointCoextensionTrace
public import Linear.NativeLocalizedSourcePoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
/-- Transfer only pointwise LOCAL data from the ORIGINAL source local
rings to the ACTUAL base-localized source,then derive the SAME ORIGINAL
coefficient point trace1. No global CM or free/flat input. Original actual
geometric chart identification,Ext comparison and top-H calibration OPEN. -/
theorem polynomial_point_original_coextension_trace_one_of_original_points
    {K S : Type u} [Field K] [CommRing S] {r : ℕ}
    [Algebra (MvPolynomial (Fin r) K) S] [Module.Finite (MvPolynomial (Fin r) K) S]
    (y : Fin r → K)
    (hred : let R := MvPolynomial (Fin r) K
      let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
      letI : m.IsPrime := RingHom.ker_isPrime _
      let Q := Localization.AtPrime m
      let S' := LocalizedModule m.primeCompl S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')))
    (hgeom : let R := MvPolynomial (Fin r) K
      let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
      letI : m.IsPrime := RingHom.ker_isPrime _
      let S' := LocalizedModule m.primeCompl S
      ∀ (p : Ideal S') (_ : p.IsMaximal),
        IsCohenMacaulayLocalRing (Localization.AtPrime
          (p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S)))) ∧
          (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime
            (p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))))) :
    let R := MvPolynomial (Fin r) K
    letI : Algebra R K := (MvPolynomial.aeval (R:=K) y).toRingHom.toAlgebra
    ∀ e : K ⊗[R] S,e ≠ 0 → e*e=e →
      ∃ z : K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))),
        coextensionOriginalResidueFiberPointEnd
          (show Function.Surjective (algebraMap R K) from
            fun a => ⟨MvPolynomial.C a,by
              change (MvPolynomial.aeval (R:=K) y) (MvPolynomial.C a)=a
              exact (MvPolynomial.aeval (R:=K) y).commutes a⟩) e z=z ∧
          coextensionOriginalBaseChangedEvaluationAtOne (R:=R) (S:=S) (K:=K) z=1 := by
  have hlocal : let R := MvPolynomial (Fin r) K
      let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
      letI : m.IsPrime := RingHom.ker_isPrime _
      let Q := Localization.AtPrime m
      let S' := LocalizedModule m.primeCompl S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) ∧
        ∀ (p : Ideal S') (_ : p.IsMaximal),
          IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
            (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) := by
    dsimp only
    let R := MvPolynomial (Fin r) K
    let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
    letI : m.IsPrime := RingHom.ker_isPrime _
    letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    refine ⟨hred,fun p hp => ?_⟩
    letI : p.IsMaximal := hp
    let q := p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))
    letI : IsCohenMacaulayLocalRing (Localization.AtPrime q) := (hgeom p hp).1
    refine ⟨nativeLocalizedSourcePoint_localCM m.primeCompl p,?_⟩
    exact (hgeom p hp).2.trans (nativeLocalizedSourcePoint_ringKrullDim m.primeCompl p).symm
  exact polynomial_point_original_coextension_trace_one y hlocal
end LinearStudy
