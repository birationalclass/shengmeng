module
public import Linear.AffineDiagonal
public import Linear.ArtinianGlobalPairing
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Tactic
/-! Actual maximal residue evaluation is surjective by Chinese remainder, and its kernel is the nilradical. A perfect multiplication functional times a generator of the nilradical annihilator is a sum of point evaluations with every weight nonzero. The socle-generation hypothesis is explicit; geometric relative Jacobian compatibility is not asserted. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
attribute [local instance] Fintype.ofFinite
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [IsArtinianRing A]
local instance : DecidableEq (MaximalSpectrum A) := Classical.decEq _

def maximalResidueEvaluation
    (q : MaximalSpectrum A → A →ₐ[K] K) : A →ₐ[K] (MaximalSpectrum A → K) := AlgHom.pi q

theorem maximalResidueEvaluation_surjective
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal) :
    Function.Surjective (maximalResidueEvaluation q) := by
  intro v
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective
    (fun i j hij => i.isCoprime_of_ne hij)
    (fun j : MaximalSpectrum A => Ideal.Quotient.mk j.asIdeal (algebraMap K A (v j)))
  refine ⟨a, ?_⟩
  funext j
  have hm : a - algebraMap K A (v j) ∈ j.asIdeal :=
    Ideal.Quotient.eq.mp (ha j)
  rw [← hq j] at hm
  change q j (a - algebraMap K A (v j)) = 0 at hm
  change q j a = v j
  simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] using hm

theorem maximalResidueEvaluation_kernel
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal) :
    RingHom.ker (maximalResidueEvaluation q).toRingHom = nilradical A := by
  rw [IsArtinianRing.nilradical_eq_iInf]
  ext a
  change (fun j => q j a) = 0 ↔ a ∈ iInf MaximalSpectrum.asIdeal
  rw [funext_iff, Ideal.mem_iInf]
  simp only [Pi.zero_apply, ← hq, RingHom.mem_ker]
  rfl

theorem maximalResidueEvaluation_selectors
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal) :
    ∃ e : MaximalSpectrum A → A, ∀ i j,
      q j (e i) = if j = i then 1 else 0 := by
  classical
  choose e he using fun i : MaximalSpectrum A =>
    maximalResidueEvaluation_surjective q hq (Pi.single i 1)
  refine ⟨e, ?_⟩
  intro i j
  simpa [maximalResidueEvaluation, Pi.single_apply] using congrFun (he i) j

theorem perfect_nilradical_socle_weighted_evaluation [IsNoetherianRing A]
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal)
    (p : PerfectMultiplicationPairing (B := K) (A := A))
    (theta : A)
    (hgen : (nilradical A).annihilator = Ideal.span {theta}) :
    ∃ lam : MaximalSpectrum A → K, (∀ j, lam j ≠ 0) ∧
      ∀ a : A, p.functional (a * theta) =
        ∑ j : MaximalSpectrum A, lam j * q j a := by
  classical
  obtain ⟨e, he⟩ := maximalResidueEvaluation_selectors q hq
  have hann : Annihilates (nilradical A) theta := by
    apply (annihilates_iff_mem_annihilator _ _).mpr
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton theta)
  have hdecomp (a : A) : a * theta = ∑ j, (q j a) • (e j * theta) := by
    have hn : a - ∑ j, (q j a) • e j ∈ nilradical A := by
      rw [← maximalResidueEvaluation_kernel q hq]
      change maximalResidueEvaluation q (a - ∑ j, (q j a) • e j) = 0
      ext i
      simp [maximalResidueEvaluation, he]
    have hm := hann _ hn
    simpa only [sub_mul, Finset.sum_mul, smul_mul_assoc, sub_eq_zero] using hm
  have hnon (i : MaximalSpectrum A) : e i * theta ≠ 0 := by
    have hi := artinian_maximal_annihilator_nonzero i.asIdeal i.isMaximal
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
    have hxn : x ∈ (nilradical A).annihilator := by
      apply Submodule.mem_annihilator.mpr
      intro a ha
      have hai : a ∈ i.asIdeal := by
        rw [IsArtinianRing.nilradical_eq_iInf] at ha
        exact Ideal.mem_iInf.mp ha i
      exact Submodule.mem_annihilator.mp hx a hai
    rw [hgen] at hxn
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hxn
    have han : Annihilates (RingHom.ker (q i).toRingHom) x := by
      apply (annihilates_iff_mem_annihilator _ _).mpr
      simpa only [hq] using hx
    have hmul : e i * x = x := by
      have hk : e i - 1 ∈ RingHom.ker (q i).toRingHom := by
        change q i (e i - 1) = 0
        simp [he]
      simpa only [sub_mul, one_mul, sub_eq_zero] using han _ hk
    intro hz
    apply hx0
    rw [← hmul, hb]
    calc e i * (theta * b) = (e i * theta) * b := (mul_assoc _ _ _).symm
         _ = 0 := by rw [hz, zero_mul]
  have hlocal (i : MaximalSpectrum A) :
      Annihilates (RingHom.ker (q i).toRingHom) (e i * theta) := by
    intro a ha
    have hn : a * e i ∈ nilradical A := by
      rw [IsArtinianRing.nilradical_eq_iInf, Ideal.mem_iInf]
      intro j
      rw [← hq j]
      change q j (a * e i) = 0
      by_cases hji : j = i
      · subst j
        change q i a = 0 at ha
        simp [ha]
      · simp [he, hji]
    simpa only [mul_assoc] using hann _ hn
  refine ⟨fun j => p.functional (e j * theta), ?_, ?_⟩
  · intro j
    exact perfect_socle_functional_nonzero (q j) p _ (hlocal j) (hnon j)
  · intro a
    rw [hdecomp, map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]

end LinearStudy
