module
public import Linear.AffineFiltered
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
variable {K ι : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial

theorem ideal_smul_top_self {A : Type*} [CommRing A] (J : Ideal A) :
    (J • (⊤ : Submodule A A) : Submodule A A) = J := by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha b _
    exact J.mul_mem_right b ha
  · intro a ha
    simpa only [smul_eq_mul, mul_one] using
      (Submodule.smul_mem_smul ha (show (1 : A) ∈ (⊤ : Submodule A A) from trivial))

theorem homogeneous_ideal_saturated_at_origin (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K))
    (s p : MvPolynomial ι K) (hs : s.coeff 0 ≠ 0) (hp : s * p ∈ I) : p ∈ I := by
  classical
  apply (MvPolynomial.mem_iff_homogeneousComponent_mem hI p).mpr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcomp : homogeneousComponent n (s * p) ∈ I :=
      MvPolynomial.homogeneousComponent_mem_of_mem hI hp n
    have he : homogeneousComponent n (s * p) =
        ∑ k ∈ Finset.range (s.totalDegree + 1),
          if k ≤ n then homogeneousComponent (n - k) p * homogeneousComponent k s else 0 := by
      conv_lhs => rw [mul_comm, ← sum_homogeneousComponent s]
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact homogeneousComponent_mul_homogeneous p _ n k (homogeneousComponent_isHomogeneous k s)
    rw [he, ← Finset.sum_erase_add _ _ (by simp : 0 ∈ Finset.range (s.totalDegree + 1))] at hcomp
    have hrest : (∑ k ∈ (Finset.range (s.totalDegree + 1)).erase 0,
          if k ≤ n then homogeneousComponent (n - k) p * homogeneousComponent k s else 0) ∈ I := by
      apply I.sum_mem
      intro k hk
      by_cases hkn : k ≤ n
      · rw [ite_eq_left hkn]
        exact I.mul_mem_right _ (ih (n-k) (by
          have : k ≠ 0 := (Finset.mem_erase.mp hk).1
          omega))
      · simp only [ite_eq_right hkn]; exact I.zero_mem
    have hmain := I.sub_mem hcomp hrest
    simp only [Nat.zero_le, ite_true, Nat.sub_zero, homogeneousComponent_zero, add_sub_cancel_left] at hmain
    have hinv := I.mul_mem_right (C ((s.coeff 0)⁻¹)) hmain
    simpa only [mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, mul_one] using hinv

theorem homogeneous_ideal_origin_localization_comap (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K)) :
    let m := RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom
    letI : m.IsPrime := RingHom.ker_isPrime _
    (I.map (algebraMap _ (Localization.AtPrime m))).comap
      (algebraMap _ (Localization.AtPrime m)) = I := by
  classical
  let m := RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom
  letI : m.IsPrime := RingHom.ker_isPrime _
  apply le_antisymm
  · intro p hp
    obtain ⟨s, hs, hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      m.primeCompl (Localization.AtPrime m) I p).mp hp
    have hn : s.coeff 0 ≠ 0 := by
      simpa [m, RingHom.mem_ker, MvPolynomial.aeval_def, MvPolynomial.eval_zero,
        MvPolynomial.constantCoeff_eq] using hs
    exact homogeneous_ideal_saturated_at_origin I hI s p hn hsp
  · exact Ideal.le_comap_map
theorem homogeneous_weaklyRegular_of_origin_localization
    (rs : List (MvPolynomial ι K))
    (hh : ∀ p ∈ rs, ∃ d, p.IsHomogeneous d)
    (hr : let m := RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom
      letI : m.IsPrime := RingHom.ker_isPrime _
      RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m)
        (rs.map (algebraMap _ (Localization.AtPrime m)))) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι K) rs := by
  classical
  let m := RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom
  letI : m.IsPrime := RingHom.ker_isPrime _
  let S := Localization.AtPrime m
  let f : MvPolynomial ι K →+* S := algebraMap _ S
  change RingTheory.Sequence.IsWeaklyRegular S (rs.map f) at hr
  refine ⟨fun i hi => ?_⟩
  let I := Ideal.ofList (rs.take i)
  have hI : I.IsHomogeneous (homogeneousSubmodule ι K) := by
    apply Ideal.homogeneous_span
    intro p hp
    obtain ⟨d, hd⟩ := hh p (List.mem_of_mem_take hp)
    exact ⟨d, hd⟩
  have hm : (I.map f).comap f = I := homogeneous_ideal_origin_localization_comap I hI
  have him : i < (rs.map f).length := by simpa using hi
  have hl := hr.regular_mod_prev i (by simpa using hi)
  change IsSMulRegular (S ⧸ (Ideal.ofList ((rs.map f).take i) •
    (⊤ : Submodule S S))) ((rs.map f)[i]) at hl
  rw [← List.map_take, ← Ideal.map_ofList] at hl
  rw [ideal_smul_top_self] at hl ⊢
  simp only [List.getElem_map] at hl
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I rs[i]).mpr
  intro p hp
  have hmap : f (rs[i]) * f p ∈ I.map f := by
    rw [← map_mul]
    exact Ideal.mem_map_of_mem f hp
  have hout : f p ∈ I.map f :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem (I.map f) (f rs[i])).mp hl _ hmap
  change p ∈ (I.map f).comap f at hout
  rwa [hm] at hout
end LinearStudy
