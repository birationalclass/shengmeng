module
public import Linear.ArbitraryParameterSocle
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

/-! Local evaluation on the actual arbitrary parameter quotient. The reduction map to ℂ, finite-dimensionality, and a normalized perfect multiplication pairing are constructed from the original complete-intersection hypotheses. This is not a construction of the globally compatible Grothendieck residue or its Euler–Jacobi sum theorem. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
namespace LinearStudy

theorem socle_linear_evaluation {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (q : A →ₐ[K] K) (delta : A)
    (hd : Annihilates (RingHom.ker q.toRingHom) delta)
    (rho : A →ₗ[K] K) (h : A) :
    rho (h * delta) = q h * rho delta := by
  have hn : h - algebraMap K A (q h) ∈ RingHom.ker q.toRingHom := by simp
  have hm := hd _ hn
  have he : h * delta = (q h) • delta := by
    simpa only [sub_mul, sub_eq_zero, Algebra.smul_def] using hm
  rw [he, map_smul, smul_eq_mul]

theorem socle_linear_evaluation_exists {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (q : A →ₐ[K] K) (delta : A)
    (hd : Annihilates (RingHom.ker q.toRingHom) delta) (hne : delta ≠ 0) :
    ∃ rho : A →ₗ[K] K, rho delta = 1 ∧ ∀ h : A, rho (h * delta) = q h := by
  obtain ⟨rho, hrho⟩ := Module.Projective.exists_dual_eq_one K hne
  refine ⟨rho, hrho, ?_⟩
  intro h
  simpa [hrho] using socle_linear_evaluation q delta hd rho h

def formalParameterConstantCoeff {r : ℕ} : ParameterRing r →ₐ[ℂ] ℂ :=
  { MvPowerSeries.constantCoeff with
    commutes' := fun k => by simp [ParameterRing, MvPowerSeries.algebraMap_apply] }

def parameterReductionToField {r : ℕ} {A : Type*} [CommRing A]
    [Algebra (ParameterRing r) A] [Algebra ℂ A]
    [IsScalarTower ℂ (ParameterRing r) A]
    (q : A →ₐ[ParameterRing r] ParameterRing r) : A →ₐ[ℂ] ℂ :=
  formalParameterConstantCoeff.comp (q.restrictScalars ℂ)

theorem parameterReductionToField_kernel {r : ℕ} {A : Type*} [CommRing A]
    [Algebra (ParameterRing r) A] [Algebra ℂ A]
    [IsScalarTower ℂ (ParameterRing r) A]
    (q : A →ₐ[ParameterRing r] ParameterRing r) :
    RingHom.ker (parameterReductionToField q).toRingHom =
      (IsLocalRing.maximalIdeal (ParameterRing r)).comap q.toRingHom := by
  change RingHom.ker (MvPowerSeries.constantCoeff.comp q.toRingHom) = _
  ext a
  change (q a).constantCoeff = 0 ↔ ¬ IsUnit (q a)
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  simp

def parameterQuotientResidueMap {r : ℕ} {A : Type*} [CommRing A]
    [Algebra (ParameterRing r) A] [Algebra ℂ A]
    [IsScalarTower ℂ (ParameterRing r) A]
    (q : A →ₐ[ParameterRing r] ParameterRing r) (J : Ideal A)
    (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r)) :
    (A ⧸ J) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ J (parameterReductionToField q) (by
    change J ≤ RingHom.ker (parameterReductionToField q).toRingHom
    rw [parameterReductionToField_kernel, ← hJ]
    exact Ideal.le_comap_map)

@[simp] theorem parameterQuotientResidueMap_mk {r : ℕ} {A : Type*} [CommRing A]
    [Algebra (ParameterRing r) A] [Algebra ℂ A]
    [IsScalarTower ℂ (ParameterRing r) A]
    (q : A →ₐ[ParameterRing r] ParameterRing r) (J : Ideal A)
    (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r)) (a : A) :
    parameterQuotientResidueMap q J hJ (Ideal.Quotient.mk J a) =
      (q a).constantCoeff := rfl

theorem parameterQuotientResidueMap_kernel {r : ℕ} {A : Type*} [CommRing A]
    [Algebra (ParameterRing r) A] [Algebra ℂ A]
    [IsScalarTower ℂ (ParameterRing r) A]
    (q : A →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical A) (J : Ideal A)
    (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r)) :
    RingHom.ker (parameterQuotientResidueMap q J hJ).toRingHom =
      (nilradical A).map (Ideal.Quotient.mk J) := by
  change RingHom.ker (Ideal.Quotient.lift J (parameterReductionToField q).toRingHom _) = _
  rw [Ideal.ker_quotient_lift, parameterReductionToField_kernel,
    ← liftedIdeal_sup_kernel q J hJ, hq, Ideal.map_sup]
  simp

theorem lemma31_local_evaluation_formula {r c : ℕ}
    (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Finite (ParameterRing r) (CompleteIntersection H)]
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    let J := Ideal.span (Set.range tau)
    let delta := Ideal.Quotient.mk J (relativeJacobian H)
    ∃ rho : (CompleteIntersection H ⧸ J) →ₗ[ℂ] ℂ,
      rho delta = 1 ∧ ∀ h : CompleteIntersection H,
        rho (Ideal.Quotient.mk J h * delta) = (q h).constantCoeff := by
  let J := Ideal.span (Set.range tau)
  have hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact htau
  let qbar : (CompleteIntersection H ⧸ J) →ₐ[ℂ] ℂ := parameterQuotientResidueMap q J hJ
  let delta : CompleteIntersection H ⧸ J := Ideal.Quotient.mk J (relativeJacobian H)
  have hd : Annihilates (nilradical (CompleteIntersection H)) (relativeJacobian H) :=
    (lemma31_annihilator_conclusion H hr hc hH q hq _).mpr ⟨1, by simp⟩
  have hdelta : Annihilates ((nilradical (CompleteIntersection H)).map
      (Ideal.Quotient.mk J)) delta :=
    (annihilates_iff_mem_annihilator _ _).mpr (annihilates_quotient_image _ J _ hd)
  have hkernel := parameterQuotientResidueMap_kernel q hq J hJ
  have hnon : delta ≠ 0 :=
    lemma31_arbitrary_parameter_jacobian_nonzero H hr hc hH q hq tau htau
  obtain ⟨rho, hrho, heval⟩ := socle_linear_evaluation_exists qbar delta
    (by rw [hkernel]; exact hdelta) hnon
  refine ⟨rho, hrho, ?_⟩
  intro h
  exact heval (Ideal.Quotient.mk J h)

theorem parameterQuotient_finiteOverComplex {r : ℕ} {A : Type*} [CommRing A]
    [IsNoetherianRing A] [Algebra (ParameterRing r) A] [Algebra ℂ A]
    [IsScalarTower ℂ (ParameterRing r) A]
    (q : A →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical A) (J : Ideal A)
    (hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r)) :
    Module.Finite ℂ (A ⧸ J) := by
  let : IsNoetherianRing (A ⧸ J) := isNoetherianRing_of_surjective A (A ⧸ J)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let qbar := parameterQuotientResidueMap q J hJ
  apply Module.finite_of_surjective_of_ker_le_nilradical qbar
  · intro k
    exact ⟨algebraMap ℂ (A ⧸ J) k, qbar.commutes k⟩
  · change RingHom.ker qbar.toRingHom ≤ nilradical (A ⧸ J)
    rw [parameterQuotientResidueMap_kernel q hq J hJ,
      ← parameterQuotient_nilradical_eq q hq J hJ]
  · exact IsNoetherian.noetherian _

theorem perfect_socle_functional_nonzero {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (q : A →ₐ[K] K)
    (p : PerfectMultiplicationPairing (B := K) (A := A))
    (delta : A) (hd : Annihilates (RingHom.ker q.toRingHom) delta)
    (hne : delta ≠ 0) : p.functional delta ≠ 0 := by
  intro hz
  apply hne
  simpa [hz] using annihilator_eq_scalar_generator q p hd

theorem kernel_socle_scalar_generation {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (q : A →ₐ[K] K) (delta : A)
    (hgen : (RingHom.ker q.toRingHom).annihilator = Ideal.span {delta}) :
    ∀ x : A, x ∈ (RingHom.ker q.toRingHom).annihilator → ∃ b : K, x = b • delta := by
  have hd : Annihilates (RingHom.ker q.toRingHom) delta := by
    apply (annihilates_iff_mem_annihilator _ _).mpr
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton delta)
  intro x hx
  rw [hgen] at hx
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton (α := A) (x := x) (y := delta)).mp hx
  refine ⟨q a, ?_⟩
  have hn : a - algebraMap K A (q a) ∈ RingHom.ker q.toRingHom := by simp
  have hm := hd _ hn
  rw [ha, mul_comm delta a]
  simpa only [sub_mul, sub_eq_zero, Algebra.smul_def] using hm

theorem exists_perfectPairing_of_kernel_socle {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [IsNoetherianRing A] [IsArtinianRing A] [IsLocalRing A]
    (q : A →ₐ[K] K) (delta : A)
    (hk : RingHom.ker q.toRingHom = nilradical A)
    (hgen : (RingHom.ker q.toRingHom).annihilator = Ideal.span {delta})
    (hne : delta ≠ 0) :
    ∃ p : PerfectMultiplicationPairing (B := K) (A := A),
      p.functional delta = 1 ∧ ∀ h : A, p.functional (h * delta) = q h := by
  have hsurj : Function.Surjective q := fun k => ⟨algebraMap K A k, q.commutes k⟩
  let : Module.Finite K A := Module.finite_of_surjective_of_ker_le_nilradical q hsurj
    (by change RingHom.ker q.toRingHom ≤ _; rw [hk]) (IsNoetherian.noetherian _)
  have hmax : RingHom.ker q.toRingHom = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective q.toRingHom hsurj)
  have hsoc := kernel_socle_scalar_generation q delta hgen
  rw [hmax] at hsoc
  have hd : Annihilates (RingHom.ker q.toRingHom) delta := by
    apply (annihilates_iff_mem_annihilator _ _).mpr
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton delta)
  obtain ⟨p, hp⟩ := exists_perfectPairing_of_scalar_socle (K := K) delta hne hsoc
  refine ⟨p, hp, ?_⟩
  intro h
  simpa [hp] using socle_linear_evaluation q delta hd p.functional h

theorem lemma31_local_perfectPairing {r c : ℕ}
    (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hH : RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H))
    [Module.Finite (ParameterRing r) (CompleteIntersection H)]
    [Module.Flat (ParameterRing r) (CompleteIntersection H)]
    (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r)
    (hq : RingHom.ker q.toRingHom = nilradical (CompleteIntersection H))
    (tau : Fin r → CompleteIntersection H)
    (htau : Ideal.span (Set.range (fun i => q (tau i))) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    let J := Ideal.span (Set.range tau)
    let delta := Ideal.Quotient.mk J (relativeJacobian H)
    ∃ p : PerfectMultiplicationPairing (B := ℂ) (A := CompleteIntersection H ⧸ J),
      p.functional delta = 1 ∧ ∀ h : CompleteIntersection H,
        p.functional (Ideal.Quotient.mk J h * delta) = (q h).constantCoeff := by
  have hgen := lemma31_arbitrary_parameter_socle_generation H hr hc hH q hq tau htau
  have hnon := lemma31_arbitrary_parameter_jacobian_nonzero H hr hc hH q hq tau htau
  dsimp only [CompleteIntersection, equationIdeal, AmbientRing, ParameterRing] at *
  let B := MvPowerSeries (Fin r) ℂ
  let A := MvPowerSeries (Fin c) B ⧸ Ideal.span (Set.range H)
  change A →ₐ[B] B at q
  change Fin r → A at tau
  let J : Ideal A := Ideal.span (Set.range tau)
  let Q := A ⧸ J
  let delta : Q := Ideal.Quotient.mk J (relativeJacobian H)
  have hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact htau
  let qbar : Q →ₐ[ℂ] ℂ := parameterQuotientResidueMap q J hJ
  let : IsNoetherianRing A := isNoetherianRing_of_surjective (AmbientRing r c) A
    (Ideal.Quotient.mk (equationIdeal H)) Ideal.Quotient.mk_surjective
  let : Module.Finite ℂ Q := parameterQuotient_finiteOverComplex q hq J hJ
  let : IsArtinianRing Q := (parameterQuotient_local_artinian q hq J hJ).1
  let : IsLocalRing Q := (parameterQuotient_local_artinian q hq J hJ).2
  have hkernel := parameterQuotientResidueMap_kernel q hq J hJ
  have hnil := parameterQuotient_nilradical_eq q hq J hJ
  obtain ⟨p, hp, heval⟩ := exists_perfectPairing_of_kernel_socle qbar delta
    (by rw [hkernel, ← hnil]) (by rw [hkernel]; exact hgen) hnon
  refine ⟨p, hp, ?_⟩
  intro h
  exact heval (Ideal.Quotient.mk J h)

end LinearStudy
