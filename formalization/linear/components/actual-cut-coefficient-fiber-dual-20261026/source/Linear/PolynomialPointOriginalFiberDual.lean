module
public import Linear.PolynomialPointOriginalFiberTrace
public import Linear.LocalizedCoextensionFiberPointTrace
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
/-- Construct the ACTUAL ORIGINAL coefficient fiber duality from ORIGINAL
reduced fiber and ORIGINAL point-local geometry. No local/global freeness
or comparison iso is an input. Preserve every original functional value,
LITERAL eval1 trace and ORIGINAL source action. This is not yet comparison
with a different fixed normalization or the SAME geometric top-H trace. -/
theorem polynomial_point_original_fiber_dual_exists
    {K S : Type u} [Field K] [CommRing S] {r : ℕ}
    [Algebra (MvPolynomial (Fin r) K) S] [Module.Finite (MvPolynomial (Fin r) K) S]
    (y : Fin r → K)
    (hred : let R := MvPolynomial (Fin r) K
      let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
      IsReduced (S ⧸ m.map (algebraMap R S)))
    (hgeom : ∀ (p : Ideal S) (_ : p.IsMaximal),
      p.comap (algebraMap (MvPolynomial (Fin r) K) S)=
        RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom →
      IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
        (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p)) :
    let R := MvPolynomial (Fin r) K
    letI : Algebra R K := (MvPolynomial.aeval (R:=K) y).toRingHom.toAlgebra
    let C := (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
    ∃ Phi : (K ⊗[R] C) ≃ₗ[K] Module.Dual K (K ⊗[R] S),
      (∀ (a : K) (ell : C) (s : S),
        Phi (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] s)=
          a*algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) s)) ∧
      (∀ z,Phi z 1=coextensionOriginalBaseChangedEvaluationAtOne z) ∧
      (∀ (s : S) z t,Phi (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s z) t=
        Phi z (t*((1:K) ⊗ₜ[R] s))) := by
  let R := MvPolynomial (Fin r) K
  let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
  have hres : Function.Surjective (MvPolynomial.aeval (R:=K) y).toRingHom :=
    fun a => ⟨MvPolynomial.C a,(MvPolynomial.aeval (R:=K) y).commutes a⟩
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hres
  let Q := Localization.AtPrime m
  letI : Algebra R K := (MvPolynomial.aeval (R:=K) y).toRingHom.toAlgebra
  let rho := polynomialPointLocalEvaluation m y rfl
  letI : Algebra Q K := rho.toRingHom.toAlgebra
  letI : IsScalarTower R Q K := IsScalarTower.of_algebraMap_eq
    (fun F => (polynomialPointLocalEvaluation_polynomial m y rfl F).symm)
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let rs := List.ofFn (fun i : Fin r =>
    algebraMap R Q (MvPolynomial.X i-MvPolynomial.C (y i)))
  have hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal Q :=
    polynomial_point_local_centered_parameters_generate y
  have hlocal : let S' := LocalizedModule m.primeCompl S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) ∧
        ∀ (p : Ideal S') (_ : p.IsMaximal),
          IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
            (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) := by
    refine ⟨?_,?_⟩
    · letI : IsReduced (S ⧸ m.map (algebraMap R S)) := hred
      exact nativeLocalizedSourceClosedFiber_reduced (S:=S) m
    · intro p hp
      letI : p.IsMaximal := hp
      let q := p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))
      have hg := hgeom q (nativeLocalizedSourcePoint_original_maximal m p)
        (nativeLocalizedSourcePoint_base_comap m p)
      letI : IsCohenMacaulayLocalRing (Localization.AtPrime q) := hg.1
      refine ⟨nativeLocalizedSourcePoint_localCM m.primeCompl p,?_⟩
      simpa only [rs,List.length_ofFn,Fintype.card_fin] using
        hg.2.trans (nativeLocalizedSourcePoint_ringKrullDim m.primeCompl p).symm
  have hfree := localized_finite_source_free_of_reduced_fiber (S:=S) m.primeCompl rs hgen hlocal
  have hinj : Function.Injective (algebraMap R Q) :=
    IsLocalization.injective Q m.primeCompl_le_nonZeroDivisors
  let Phi := localizedCoextensionOriginalDualTensorEquiv (K:=K) m.primeCompl hfree hinj
  refine ⟨Phi,?_,?_,?_⟩
  · exact localizedCoextensionOriginalDualTensorEquiv_tmul_apply m.primeCompl hfree hinj
  · exact localizedCoextensionOriginalDualTensorEquiv_evaluation m.primeCompl hfree hinj
  · exact localizedCoextensionOriginalDualTensorEquiv_scalar_naturality m.primeCompl hfree hinj
end LinearStudy
