import ChainProducts
import JordanChains

noncomputable section
namespace JordanSize
variable {K A V W Z : Type*} [Field K] [CharZero K]
 [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
 [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

/-- Lemma 1.2, including the exact coefficient and the produced independent chain.
Lengths are p+1, q+1; their product length is p+q+1. -/
theorem weighted_product (B : A →ₗ[K] V →ₗ[K] W →ₗ[K] Z)
    (P : Module.End K A) (T : Module.End K V)
    (S : Module.End K W) (R : Module.End K Z)
    (h : ∀ w x y, R (B w x y) = B (P w) (T x) (S y))
    (c a b : K) (hc : c ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (p q : ℕ) (w : A) (x : V) (y : W)
    (hw : P w = c • w)
    (hx : ((T-a • 1)^(p+1)) x = 0)
    (hy : ((S-b • 1)^(q+1)) y = 0) :
    ((R-(c*a*b) • 1)^(p+q)) (B w x y) =
      ((Nat.choose (p+q) p : K) * c^(p+q) * b^p * a^q) •
        B w (((T-a • 1)^p) x) (((S-b • 1)^q) y) ∧
    ((R-(c*a*b) • 1)^(p+q+1)) (B w x y) = 0 ∧
    (B w (((T-a • 1)^p) x) (((S-b • 1)^q) y) ≠ 0 →
      Nonempty (JordanChain R (c*a*b) (p+q+1))) := by
  let C : Module.End K Z := c⁻¹ • R
  have he : ∀ x y, C (B w x y) = B w (T x) (S y) := by
    intro x y
    simp [C, h, hw, hc]
  have hs : R-(c*a*b) • 1 = c • (C-(a*b) • 1) := by
    dsimp [C]
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
    congr 1
    ring
  have ht := product_top (B w) T S C he a b p q x y hx hy
  have hz := generalizedProduct (B w) T S C he a b (p+1) (q+1) x y hx hy
  simp only [show p+1+(q+1)-1=p+q+1 by omega] at hz
  have ht' : ((R-(c*a*b) • 1)^(p+q)) (B w x y) =
      ((Nat.choose (p+q) p : K) * c^(p+q) * b^p * a^q) •
        B w (((T-a • 1)^p) x) (((S-b • 1)^q) y) := by
    rw [hs, smul_pow, LinearMap.smul_apply, ht, smul_smul]
    congr 1
    ring
  have hz' : ((R-(c*a*b) • 1)^(p+q+1)) (B w x y) = 0 := by
    rw [hs, smul_pow, LinearMap.smul_apply, hz, smul_zero]
  refine ⟨ht', hz', ?_⟩
  intro hne
  have hchoose : (Nat.choose (p+q) p : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ p+q by omega)).ne'
  have htop : ((R-(c*a*b) • 1)^(p+q)) (B w x y) ≠ 0 := by
    rw [ht']
    exact smul_ne_zero (by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hchoose
        (pow_ne_zero _ hc)) (pow_ne_zero _ hb)) (pow_ne_zero _ ha)) hne
  exact ⟨chainFromGenerator R (c*a*b) (p+q+1) (B w x y) hz'
    (by simpa using htop)⟩

theorem lemma_1_2 (B : A →ₗ[K] V →ₗ[K] W →ₗ[K] Z)
    (P : A ≃ₗ[K] A) (T : V ≃ₗ[K] V)
    (S : W ≃ₗ[K] W) (R : Module.End K Z)
    (h : ∀ w x y, R (B w x y) = B (P w) (T x) (S y))
    (c a b : K) (p q : ℕ) (w : A) (hw0 : w ≠ 0)
    (hw : P w = c • w)
    (C : JordanChain T.toLinearMap a (p+1))
    (D : JordanChain S.toLinearMap b (q+1)) :
    ((R-(c*a*b) • 1)^(p+q))
        (B w (C.vectors (Fin.last p)) (D.vectors (Fin.last q))) =
      ((Nat.choose (p+q) p : K) * c^(p+q) * b^p * a^q) •
        B w (C.vectors 0) (D.vectors 0) ∧
    ((R-(c*a*b) • 1)^(p+q+1))
        (B w (C.vectors (Fin.last p)) (D.vectors (Fin.last q))) = 0 ∧
    (B w (C.vectors 0) (D.vectors 0) ≠ 0 →
      Nonempty (JordanChain R (c*a*b) (p+q+1))) := by
  have hc : c ≠ 0 := by
    intro hc
    exact hw0 (P.injective (by simpa [hc] using hw))
  have ha : a ≠ 0 := by
    intro ha
    exact C.endpoint_ne_zero (T.injective (by simpa [ha] using C.relation 0))
  have hb : b ≠ 0 := by
    intro hb
    exact D.endpoint_ne_zero (S.injective (by simpa [hb] using D.relation 0))
  simpa only [C.top_powers.2, D.top_powers.2] using
    weighted_product B P.toLinearMap T.toLinearMap S.toLinearMap R h c a b
      hc ha hb p q w (C.vectors (Fin.last p)) (D.vectors (Fin.last q)) hw
      C.top_powers.1 D.top_powers.1

end JordanSize
