module
public import Linear.HomogeneousLocalization
public import Linear.Vendor.CM.CohenMacaulayCatenary
public import Linear.Vendor.CM.CohenMacaulayPolynomial
public import Linear.PolynomialRegular
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
open MvPolynomial RingTheory.Sequence
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem field_isCohenMacaulay : IsCohenMacaulayRing K := by
  letI : IsCohenMacaulayLocalRing K :=
    isCohenMacaulayLocalRing_of_ringKrullDim_le_depth K (by
      rw [ringKrullDim_eq_zero_of_field]
      exact WithBot.coe_le_coe.mpr zero_le)
  exact IsCohenMacaulayRing.of_isCohenMacaulayLocalRing K

omit [IsAlgClosed K] in
theorem polynomial_origin_height (n : ℕ) :
    let m := RingHom.ker (MvPolynomial.aeval (R := K) (0 : Fin n → K)).toRingHom
    m.height = n := by
  let m := RingHom.ker (MvPolynomial.aeval (R := K) (0 : Fin n → K)).toRingHom
  let rs := List.ofFn (MvPolynomial.X (σ := Fin n) (R := K))
  have hm : Ideal.ofList rs = m := by
    change Ideal.span {p | p ∈ List.ofFn (MvPolynomial.X (σ := Fin n) (R := K))} = m
    have hl : {p | p ∈ List.ofFn (MvPolynomial.X (σ := Fin n) (R := K))} =
        Set.range (MvPolynomial.X (σ := Fin n) (R := K)) := by ext p; simp
    rw [hl]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      simp [m, RingHom.mem_ker]
    · intro p hp
      have hz : p.coeff 0 = 0 := by
        simpa [m, RingHom.mem_ker, MvPolynomial.aeval_def, MvPolynomial.eval_zero,
          MvPolynomial.constantCoeff_eq] using hp
      change p ∈ MvPolynomial.idealOfVars (Fin n) K
      rw [← pow_one (MvPolynomial.idealOfVars (Fin n) K), MvPolynomial.mem_pow_idealOfVars_iff']
      intro x hx
      have : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega : x.degree = 0)
      simpa [this] using hz
  have hne : Ideal.ofList rs ≠ ⊤ := by
    rw [hm]
    exact (RingHom.ker_isPrime (MvPolynomial.aeval (R := K) (0 : Fin n → K)).toRingHom).ne_top
  have ht := Ideal.ofList_height_eq_length_of_isWeaklyRegular rs (polynomial_variables_regular n).1 hne
  change m.height = n
  rw [← hm]
  simpa only [rs,List.length_ofFn,Fintype.card_fin] using ht

theorem homogeneous_origin_regular (n : ℕ) (H : Fin n → MvPolynomial (Fin n) K)
    (hh : ∀ i, ∃ d, (H i).IsHomogeneous d)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range H)) = {0}) :
    IsRegular (MvPolynomial (Fin n) K) (List.ofFn H) := by
  classical
  let R := MvPolynomial (Fin n) K
  let m : Ideal R := RingHom.ker (MvPolynomial.aeval (R := K) (0 : Fin n → K)).toRingHom
  letI : m.IsPrime := RingHom.ker_isPrime _
  let S := Localization.AtPrime m
  let f : R →+* S := algebraMap R S
  let rs := List.ofFn H
  let I := Ideal.ofList rs
  have hlist : I = Ideal.span (Set.range H) := by
    change Ideal.span {p | p ∈ List.ofFn H} = Ideal.span (Set.range H)
    congr 1
    ext p
    simp
  have hrad : I.radical = m := by
    rw [hlist]
    exact polynomial_origin_radical (Ideal.span (Set.range H)) hz
  letI : IsCohenMacaulayRing K := field_isCohenMacaulay
  letI : IsCohenMacaulayRing R := MvPolynomial.isCM_of_isCM_of_finite K (Fin n)
  letI : IsCohenMacaulayLocalRing S :=
    (isCohenMacaulayRing_def R).mp inferInstance m inferInstance
  have hradS : (I.map f).radical = IsLocalRing.maximalIdeal S := by
    rw [← IsLocalization.map_radical m.primeCompl S I, hrad]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal m S
  have hmin : IsLocalRing.maximalIdeal S ∈ (Ideal.ofList (rs.map f)).minimalPrimes := by
    rw [← Ideal.map_ofList, ← Ideal.radical_minimalPrimes, hradS,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hdim : ((rs.map f).length : WithBot ℕ∞) = ringKrullDim S := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m S, polynomial_origin_height n]
    simp [rs]
  have hlocal := isRegular_of_maximalIdeal_mem_ofList_minimalPrimes (rs.map f) hmin hdim
  refine ⟨homogeneous_weaklyRegular_of_origin_localization rs ?_ hlocal.1, ?_⟩
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hh i
  · rw [ideal_smul_top_self]
    have hne : I ≠ ⊤ := by
      intro he
      have hm := (show m.IsPrime from inferInstance).ne_top
      apply hm
      rw [← hrad,he,Ideal.radical_top]
    exact hne.symm

end LinearStudy
