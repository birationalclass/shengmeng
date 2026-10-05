import MultilinearLogarithm
import IntegerFlow
import JordanProfiles
noncomputable section
universe u
namespace JordanSize
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
variable {V : Type u} [AddCommGroup V] [Module K V] [Module ℚ V]
 [IsScalarTower ℚ K V] [FiniteDimensional K V] [Nontrivial V]
 {T : Module.End K V}

lemma scalar_unipotent (F : Factors T) (d : K) (hd : d ≠ 0) (hT : T = d • 1) :
    F.u = 1 := by
  ext x
  have hx : x ∈ T.maxGenEigenspace d := by
    apply T.mem_genEigenspace.mpr
    refine ⟨1, le_top, ?_⟩
    simp [hT]
  have h := F.u_apply hx
  simpa [hT, smul_smul, hd] using h

/-- All linear conclusions of JS-lemmas Lemma 1.1.
`largestJordanBlock` uses the generalized-eigenspace annihilation definition;
`kernelProfile` records the whole Jordan size profile, not only its maximum. -/
def LogarithmicChainStatement (F : Factors T) : Prop :=
  IsNilpotent F.log ∧
  (∀ ℓ : ℤ, ((F.u_unit.unit^ℓ : (Module.End K V)ˣ) : Module.End K V) =
    IsNilpotent.exp ((ℓ : ℚ) • F.log)) ∧
  (∃ m : ℕ, F.u-1 = F.log * expQuotient F.log m ∧
    IsUnit (expQuotient F.log m)) ∧
  (∀ j : ℕ, LinearMap.ker ((F.u-1)^j) = LinearMap.ker (F.log^j) ∧
    LinearMap.range ((F.u-1)^j) = LinearMap.range (F.log^j)) ∧
  (largestJordanBlock T = 1 + (nilpotencyClass F.log-1) ∧
    F.log^(largestJordanBlock T-1) ≠ 0 ∧ F.log^(largestJordanBlock T) = 0 ∧
    (∀ j, largestJordanBlock T ≤ j → F.log^j = 0)) ∧
  (∀ a : ℕ, 0 < a → (F.power a).log = (a : ℚ) • F.log ∧
    (∀ j, LinearMap.ker (((F.power a).u-1)^j) = LinearMap.ker ((F.u-1)^j) ∧
      LinearMap.range (((F.power a).u-1)^j) = LinearMap.range ((F.u-1)^j)) ∧
    (∀ j, kernelProfile (F.power a).log j = kernelProfile F.log j) ∧
    (∀ r, blockMultiplicity (F.power a).log r = blockMultiplicity F.log r) ∧
    largestJordanBlock (T^a) = largestJordanBlock T) ∧
  (∀ d : K, d ≠ 0 → T = d • 1 → F.u = 1)

theorem lemma_1_1_linear (F : Factors T) : LogarithmicChainStatement F := by
  refine ⟨F.log_nilpotent, ?_, ?_, ?_, largestJordanBlock_characterization F, ?_,
    scalar_unipotent F⟩
  · intro ℓ
    exact exp_integer F.log F.log_nilpotent F.u_unit.unit
      (F.u_unit.unit_spec.trans F.exp_log.symm) ℓ
  · obtain ⟨m, hm⟩ := F.log_nilpotent
    refine ⟨m, ?_, expQuotient_unit F.log ⟨m,hm⟩ m⟩
    simpa only [F.exp_log] using exp_sub_one_factor F.log m
      (pow_eq_zero_of_le (by omega) hm)
  · intro j
    have h := exponentialChains F.log F.log_nilpotent j
    rw [F.exp_log] at h
    exact ⟨h.1, h.2.1⟩
  · intro a ha
    refine ⟨F.log_power a, ?_, power_kernelProfile F a ha,
      power_blockMultiplicity F a ha, power_largestJordanBlock F a ha⟩
    intro j
    have h1 := exponentialChains (F.power a).log (F.power a).log_nilpotent j
    have h2 := exponentialChains F.log F.log_nilpotent j
    have h3 := nonzero_smul_filtrations F.log (a : ℚ) (by exact_mod_cast ha.ne') j
    rw [(F.power a).exp_log, F.log_power] at h1
    rw [F.exp_log] at h2
    exact ⟨h1.1.trans (h3.1.trans h2.1.symm),
      h1.2.1.trans (h3.2.1.trans h2.2.1.symm)⟩

/-- The complete linear and product statement, for any given multilinear map.
Only finite dimensionality, invertibility and the displayed equivariance
are assumed; the unipotent and Leibniz conclusions are proved. -/
theorem lemma_1_1 (n : ℕ) {M : Fin n → Type u} {Z : Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, Module ℚ (M i)] [∀ i, IsScalarTower ℚ K (M i)]
    [∀ i, FiniteDimensional K (M i)] [∀ i, Nontrivial (M i)]
    [AddCommGroup Z] [Module K Z] [Module ℚ Z] [IsScalarTower ℚ K Z]
    [FiniteDimensional K Z] [Nontrivial Z]
    (B : MultilinearMap K M Z) (T : ∀ i, Module.End K (M i))
    (R : Module.End K Z) (hT : ∀ i, IsUnit (T i)) (hR : IsUnit R)
    (hB : ∀ x, R (B x) = B (fun i => T i (x i))) :
    (∀ i, LogarithmicChainStatement (jordanFactors (T i) (hT i))) ∧
    LogarithmicChainStatement (jordanFactors R hR) ∧
    (∀ x, (jordanFactors R hR).u (B x) =
      B (fun i => (jordanFactors (T i) (hT i)).u (x i))) ∧
    (∀ x, (jordanFactors R hR).log (B x) =
      ∑ i, B (Function.update x i ((jordanFactors (T i) (hT i)).log (x i)))) := by
  refine ⟨fun i => lemma_1_1_linear _, lemma_1_1_linear _, ?_, ?_⟩
  · exact unipotent_multilinear n B T R _ _ hB
  · exact logarithm_multilinear n B T R _ _ hB
end JordanSize
#print axioms JordanSize.lemma_1_1_linear
#print axioms JordanSize.lemma_1_1
