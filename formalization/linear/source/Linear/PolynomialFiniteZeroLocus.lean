module
public import Linear.PolynomialOriginFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]

/-- A finite actual zero locus gives a finite-dimensional quotient even
when its scheme has nilpotents. Finiteness is lifted from the radical quotient. -/
theorem polynomialQuotient_finite_of_finite_zeroLocus
    (I : Ideal (MvPolynomial σ K)) (hZ : (MvPolynomial.zeroLocus K I).Finite) :
    Module.Finite K (MvPolynomial σ K ⧸ I) := by
  classical
  let S := MvPolynomial.zeroLocus K I
  letI : Finite S := hZ.to_subtype
  letI : Fintype S := Fintype.ofFinite S
  let Q := MvPolynomial σ K ⧸ I
  let Qr := MvPolynomial σ K ⧸ I.radical
  let E : MvPolynomial σ K →ₐ[K] (S → K) :=
    AlgHom.pi (fun x : S => MvPolynomial.aeval x.val)
  have hEr : ∀ p ∈ I.radical, E p = 0 := by
    intro p hp
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I] at hp
    funext x
    exact hp x.val x.property
  let e : Qr →ₐ[K] (S → K) := Ideal.Quotient.liftₐ I.radical E hEr
  have he : Function.Injective e := by
    apply (injective_iff_map_eq_zero e).mpr
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I]
    intro x hx
    exact congrFun ha ⟨x, hx⟩
  letI : Module.Finite K Qr := Module.Finite.of_injective e.toLinearMap he
  let q : Q →ₐ[K] Qr := Ideal.Quotient.factorₐ K (show I ≤ I.radical from Ideal.le_radical)
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective Ideal.le_radical
  have hk : RingHom.ker q.toRingHom ≤ nilradical Q := by
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hp : p ∈ I.radical := Ideal.Quotient.eq_zero_iff_mem.mp ha
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hp
    apply mem_nilradical.mpr
    refine ⟨m, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  exact Module.finite_of_surjective_of_ker_le_nilradical q hq hk
    (IsNoetherian.noetherian (RingHom.ker q.toRingHom))

end LinearStudy
