import ChainTransport
import KernelStability

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JordanSize
variable {K V W Z : Type*} [Field K]
 [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
 [AddCommGroup Z] [Module K Z]

lemma invertible_zero_profile [FiniteDimensional K V] (T : V ≃ₗ[K] V) (j : ℕ) :
    Module.finrank K (LinearMap.ker ((T.toLinearMap-(0:K) • 1)^j)) = 0 := by
  have hu : IsUnit T.toLinearMap :=
    (Module.End.isUnit_iff _).mpr T.bijective
  have he : T.toLinearMap-(0:K) • 1 = T.toLinearMap := by simp
  rw [he]
  rw [(LinearMap.isUnit_iff_ker_eq_bot _).mp (hu.pow j)]
  simp

theorem pairing_bounds [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K) (hd : d ≠ 0)
    (h : ∀ x y, e (S y) (T x) = d * e y x) (j : ℕ) :
    JordanBound T.toLinearMap j ↔ JordanBound S.toLinearMap j := by
  rw [jordanBound_stability, jordanBound_stability]
  have hf (a : K) (ha : a ≠ 0) (m : ℕ) :=
    pairing_kernel_profile T S.toLinearMap e d a hd ha h m
  constructor
  · intro ht b
    by_cases hb : b=0
    · subst b; rw [invertible_zero_profile, invertible_zero_profile]
    · have ha : d/b ≠ 0 := div_ne_zero hd hb
      have he : d/(d/b)=b := by field_simp
      rw [← he, hf (d/b) ha (j+1), hf (d/b) ha j, ht]
  · intro hs a
    by_cases ha : a=0
    · subst a; rw [invertible_zero_profile, invertible_zero_profile]
    · rw [← hf a ha (j+1), ← hf a ha j, hs]

theorem pairing_largest [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K) (hd : d ≠ 0)
    (h : ∀ x y, e (S y) (T x) = d * e y x) :
    largestJordanBlock T.toLinearMap = largestJordanBlock S.toLinearMap := by
  unfold largestJordanBlock
  congr 1
  ext j
  exact pairing_bounds T S e d hd h j

/-- Lemma 1.3: the contragredient identity and all block profiles.
The transport part is supplied by `transportChain`, with no injectivity
assumption on the transporting linear map. -/
theorem lemma_1_3_pairing [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K) (hd : d ≠ 0)
    (h : ∀ x y, e (S y) (T x) = d * e y x) :
    e.toLinearMap.comp S.toLinearMap =
      (d • T.symm.toLinearMap.dualMap).comp e.toLinearMap ∧
    (∀ a : K, a ≠ 0 → ∀ j : ℕ,
      Module.finrank K (LinearMap.ker ((S.toLinearMap-(d/a) • 1)^j)) =
        Module.finrank K (LinearMap.ker ((T.toLinearMap-a • 1)^j))) ∧
    largestJordanBlock T.toLinearMap = largestJordanBlock S.toLinearMap := by
  exact ⟨pairing_operator T S.toLinearMap e d h,
    fun a ha j => pairing_kernel_profile T S.toLinearMap e d a hd ha h j,
    pairing_largest T S e d hd h⟩

lemma chain_profile_jump [FiniteDimensional K V]
    (T : Module.End K V) (a : K) {r : ℕ} (C : JordanChain T a (r+1)) :
    Module.finrank K (LinearMap.ker ((T-a • 1)^r)) <
      Module.finrank K (LinearMap.ker ((T-a • 1)^(r+1))) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne (power_ker_mono _ (show r ≤ r+1 by omega))
  intro he
  have hx : C.vectors (Fin.last r) ∈ LinearMap.ker ((T-a • 1)^r) := by
    rw [he]
    exact C.top_powers.1
  exact C.endpoint_ne_zero (C.top_powers.2.symm.trans hx)

lemma chain_from_profile [FiniteDimensional K V]
    (T : Module.End K V) (a : K) (r : ℕ)
    (h : Module.finrank K (LinearMap.ker ((T-a • 1)^r)) <
      Module.finrank K (LinearMap.ker ((T-a • 1)^(r+1)))) :
    Nonempty (JordanChain T a (r+1)) := by
  have hn : ¬LinearMap.ker ((T-a • 1)^(r+1)) ≤ LinearMap.ker ((T-a • 1)^r) := by
    intro he
    exact Nat.not_le_of_lt h (Submodule.finrank_mono he)
  change ¬∀ x, x ∈ LinearMap.ker ((T-a • 1)^(r+1)) →
    x ∈ LinearMap.ker ((T-a • 1)^r) at hn
  push_neg at hn
  obtain ⟨x,hzero,htop⟩ := hn
  exact ⟨chainFromGenerator T a (r+1) x hzero (by simpa using htop)⟩

theorem pairing_transfer_chain [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K) (hd : d ≠ 0)
    (h : ∀ x y, e (S y) (T x) = d * e y x)
    (b : K) {r : ℕ} (C : JordanChain S.toLinearMap b (r+1)) :
    Nonempty (JordanChain T.toLinearMap (d/b) (r+1)) := by
  have hb : b ≠ 0 := by
    intro hb
    exact C.endpoint_ne_zero (S.injective (by simpa [hb] using C.relation 0))
  have ha : d/b ≠ 0 := div_ne_zero hd hb
  have he : d/(d/b)=b := by field_simp
  apply chain_from_profile
  have hj := chain_profile_jump S.toLinearMap b C
  rw [← he,
    pairing_kernel_profile T S.toLinearMap e d (d/b) hd ha h r,
    pairing_kernel_profile T S.toLinearMap e d (d/b) hd ha h (r+1)] at hj
  exact hj

/-- All clauses of Lemma 1.3, including normalized transport vectors and
transfer back through the perfect pairing. -/
theorem lemma_1_3 [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K) (hd : d ≠ 0)
    (h : ∀ x y, e (S y) (T x) = d * e y x)
    (R : Module.End K Z) (L : V →ₗ[K] Z) (c a : K) (hc : c ≠ 0)
    (hL : ∀ x, R (L x) = c • L (T x))
    {r : ℕ} (C : JordanChain T.toLinearMap a (r+1))
    (hend : L (C.vectors 0) ≠ 0) :
    e.toLinearMap.comp S.toLinearMap =
      (d • T.symm.toLinearMap.dualMap).comp e.toLinearMap ∧
    (∀ b : K, b ≠ 0 → ∀ j : ℕ,
      Module.finrank K (LinearMap.ker ((S.toLinearMap-(d/b) • 1)^j)) =
        Module.finrank K (LinearMap.ker ((T.toLinearMap-b • 1)^j))) ∧
    largestJordanBlock T.toLinearMap = largestJordanBlock S.toLinearMap ∧
    (∃ D : JordanChain R (c*a) (r+1),
      ∀ i, D.vectors i = (c⁻¹)^i.val • L (C.vectors i)) ∧
    (∀ b : K, ∀ D : JordanChain S.toLinearMap b (r+1),
      Nonempty (JordanChain T.toLinearMap (d/b) (r+1))) := by
  have hp := lemma_1_3_pairing T S e d hd h
  exact ⟨hp.1,hp.2.1,hp.2.2,
    ⟨transportChain T.toLinearMap R L c a hc hL C hend,fun _ => rfl⟩,
    fun b D => pairing_transfer_chain T S e d hd h b D⟩

end JordanSize
