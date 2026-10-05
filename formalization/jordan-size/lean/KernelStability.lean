import PerfectPairing

noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma power_ker_mono (D : Module.End K V) {j m : ℕ} (h : j ≤ m) :
    LinearMap.ker (D^j) ≤ LinearMap.ker (D^m) := by
  intro x hx
  change (D^j) x = 0 at hx
  change (D^m) x = 0
  rw [show m=(m-j)+j by omega, pow_add, Module.End.mul_apply, hx, map_zero]

lemma stable_ker_all (D : Module.End K V) (j : ℕ)
    (h : LinearMap.ker (D^(j+1)) ≤ LinearMap.ker (D^j)) :
    ∀ m, LinearMap.ker (D^m) ≤ LinearMap.ker (D^j) := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hx' : x=0 := by simpa using hx
    simp [hx']
  | succ m ih =>
    intro x hx
    apply h
    change (D^(j+1)) x = 0
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    simpa only [LinearMap.mem_ker, pow_succ, Module.End.mul_apply] using hx

lemma jordanBound_stability [FiniteDimensional K V] (T : Module.End K V) (j : ℕ) :
    JordanBound T j ↔ ∀ a : K,
      Module.finrank K (LinearMap.ker ((T-a • 1)^(j+1))) =
        Module.finrank K (LinearMap.ker ((T-a • 1)^j)) := by
  constructor
  · intro h a
    have he : LinearMap.ker ((T-a • 1)^(j+1)) =
        LinearMap.ker ((T-a • 1)^j) := by
      apply le_antisymm
      · intro x hx
        exact h a x ((Module.End.mem_genEigenspace_top).mpr ⟨j+1,hx⟩)
      · exact power_ker_mono _ (by omega)
    rw [he]
  · intro h a x hx
    have hker : LinearMap.ker ((T-a • 1)^(j+1)) ≤ LinearMap.ker ((T-a • 1)^j) := by
      have he := Submodule.eq_of_le_of_finrank_eq
        (power_ker_mono (T-a • 1) (show j ≤ j+1 by omega)) (h a).symm
      exact he.ge
    obtain ⟨m,hm⟩ := (Module.End.mem_genEigenspace_top).mp hx
    exact stable_ker_all (T-a • 1) j hker m hm

lemma largestJordanBlock_bound [FiniteDimensional K V] (T : Module.End K V) :
    JordanBound T (largestJordanBlock T) := by
  have hn : {j | JordanBound T j}.Nonempty := by
    refine ⟨Module.finrank K V, ?_⟩
    intro a x hx
    rw [T.maxGenEigenspace_eq_genEigenspace_finrank a] at hx
    simpa only [Module.End.genEigenspace_nat, LinearMap.mem_ker] using hx
  exact Nat.sInf_mem hn

end JordanSize
