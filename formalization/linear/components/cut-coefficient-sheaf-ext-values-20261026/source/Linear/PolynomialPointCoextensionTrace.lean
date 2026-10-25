module
public import Linear.LocalizedCoextensionReducedFiberTrace
public import Linear.PolynomialPointEvaluation
public import Linear.PolynomialLocalParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
/-- The ACTUAL centered coordinate parameters generate the ACTUAL local
maximal ideal of a polynomial rational point. Reuse the original point-kernel theorem. -/
theorem polynomial_point_local_centered_parameters_generate
    {K : Type u} [Field K] {r : ℕ} (y : Fin r → K) :
    let R := MvPolynomial (Fin r) K
    let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
    letI : m.IsPrime := RingHom.ker_isPrime _
    Ideal.ofList (List.ofFn (fun i : Fin r =>
      algebraMap R (Localization.AtPrime m) (MvPolynomial.X i-MvPolynomial.C (y i))))=
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  intro R m
  letI : m.IsPrime := RingHom.ker_isPrime _
  let Q := Localization.AtPrime m
  have hh := congrArg (fun J : Ideal R => J.map (algebraMap R Q))
    (polynomial_point_kernel_eq_span_centered_coordinates y)
  rw [Ideal.map_span,← Set.range_comp'] at hh
  have hl : Ideal.ofList (List.ofFn (fun i : Fin r =>
      algebraMap R Q (MvPolynomial.X i-MvPolynomial.C (y i))))=
      Ideal.span (Set.range (fun i : Fin r =>
        algebraMap R Q (MvPolynomial.X i-MvPolynomial.C (y i)))) := by
    simp [Ideal.ofList,List.mem_ofFn,Set.range]
  exact hl.trans (hh.symm.trans Localization.AtPrime.map_eq_maximalIdeal)
/-- At an ACTUAL polynomial base point,derive all base parameters,
residue surjectivity and localization injectivity. Only ACTUAL localized
source reducedness and pointwise LOCAL CM/dimension remain explicit.
The SAME ORIGINAL C fiber/projector and LITERAL eval1 base change are used.
Original geometric source-chart instantiation and Ext/top-H calibration
are NOT asserted by this algebraic theorem. -/
theorem polynomial_point_original_coextension_trace_one
    {K S : Type u} [Field K] [CommRing S] {r : ℕ}
    [Algebra (MvPolynomial (Fin r) K) S] [Module.Finite (MvPolynomial (Fin r) K) S]
    (y : Fin r → K)
    (hlocal : let R := MvPolynomial (Fin r) K
      let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
      letI : m.IsPrime := RingHom.ker_isPrime _
      let Q := Localization.AtPrime m
      let S' := LocalizedModule m.primeCompl S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) ∧
        ∀ (p : Ideal S') (_ : p.IsMaximal),
          IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
            (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p)) :
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
  dsimp only
  let R := MvPolynomial (Fin r) K
  let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
  letI : m.IsPrime := RingHom.ker_isPrime _
  let Q := Localization.AtPrime m
  letI : Algebra R K := (MvPolynomial.aeval (R:=K) y).toRingHom.toAlgebra
  let rho := polynomialPointLocalEvaluation m y rfl
  letI : Algebra Q K := rho.toRingHom.toAlgebra
  letI : IsScalarTower R Q K := IsScalarTower.of_algebraMap_eq
    (fun F => (polynomialPointLocalEvaluation_polynomial m y rfl F).symm)
  let rs := List.ofFn (fun i : Fin r =>
    algebraMap R Q (MvPolynomial.X i-MvPolynomial.C (y i)))
  have hgen : Ideal.ofList rs=IsLocalRing.maximalIdeal Q :=
    polynomial_point_local_centered_parameters_generate y
  have hloc : let S' := LocalizedModule m.primeCompl S
      letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
      letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=m.primeCompl) Q
      IsReduced (S' ⧸ (IsLocalRing.maximalIdeal Q).map (algebraMap Q S')) ∧
        ∀ (p : Ideal S') (_ : p.IsMaximal),
          IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
            (rs.length : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p) := by
    refine ⟨hlocal.1,fun p hp => ⟨(hlocal.2 p hp).1,?_⟩⟩
    simpa only [rs,List.length_ofFn,Fintype.card_fin] using (hlocal.2 p hp).2
  have hinj : Function.Injective (algebraMap R Q) :=
    IsLocalization.injective Q m.primeCompl_le_nonZeroDivisors
  have hres : Function.Surjective (algebraMap R K) := fun a => ⟨MvPolynomial.C a,by
              change (MvPolynomial.aeval (R:=K) y) (MvPolynomial.C a)=a
              exact (MvPolynomial.aeval (R:=K) y).commutes a⟩
  intro e he hi
  exact original_coextension_point_trace_one_of_local_reduced_fiber
    m.primeCompl rs hgen hloc hinj hres e he hi
end LinearStudy
