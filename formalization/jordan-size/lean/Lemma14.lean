import Lemma12
import Lemma13
import ConjugateChains

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JordanSize
variable {K A V W : Type*} [Field K] [CharZero K]
 [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
 [AddCommGroup W] [Module K W]
 [FiniteDimensional K V] [FiniteDimensional K W]

lemma product_endpoint_vanish
    (B : A →ₗ[K] V →ₗ[K] V →ₗ[K] W)
    (P : A ≃ₗ[K] A) (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (hB : ∀ w x y, S (B w x y) = B (P w) (T x) (T y))
    (r : ℕ) (hr : 1 ≤ r) (hb : JordanBound S.toLinearMap (r+1))
    (a b c : K) (ha : a ≠ 0) (hb' : b ≠ 0)
    (C : JordanChain T.toLinearMap a (r+1))
    (D : JordanChain T.toLinearMap b (r+1))
    (w : A) (hw : P w = c • w) : B w (C.vectors 0) (D.vectors 0) = 0 := by
  by_cases hw0 : w=0
  · simp [hw0]
  have hc : c ≠ 0 := by
    intro hc
    have hz : P w = P 0 := by simpa [hc] using hw
    exact hw0 (P.injective hz)
  have hp := weighted_product B P.toLinearMap T.toLinearMap T.toLinearMap
    S.toLinearMap hB c a b hc ha hb' r r w
    (C.vectors (Fin.last r)) (D.vectors (Fin.last r)) hw
    C.top_powers.1 D.top_powers.1
  have hgen : B w (C.vectors (Fin.last r)) (D.vectors (Fin.last r)) ∈
      Module.End.maxGenEigenspace S.toLinearMap (c*a*b) := by
    exact (Module.End.mem_genEigenspace_top).mpr ⟨r+r+1,hp.2.1⟩
  have hz := hb (c*a*b) _ hgen
  have hz' : ((S.toLinearMap-(c*a*b) • 1)^(r+r))
      (B w (C.vectors (Fin.last r)) (D.vectors (Fin.last r))) = 0 := by
    rw [show r+r=(r+r-(r+1))+(r+1) by omega,
      pow_add, Module.End.mul_apply, hz, map_zero]
  rw [hp.1, C.top_powers.2, D.top_powers.2] at hz'
  have hchoose : (Nat.choose (r+r) r : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show r ≤ r+r by omega)).ne'
  exact (smul_eq_zero.mp hz').resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hchoose
      (pow_ne_zero _ hc)) (pow_ne_zero _ hb')) (pow_ne_zero _ ha))

/-- Corollary 1.4, for a longest chain and its semilinear conjugate.
Set K=C and σ=complex conjugation for the manuscript statement.
The weight space is the ordinary vector space N^(n-3), and W=N^(n-1). -/
theorem lemma_1_4
    (B : A →ₗ[K] V →ₗ[K] V →ₗ[K] W)
    (P : A ≃ₗ[K] A) (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K) (hd : d ≠ 0)
    (hpair : ∀ x y, e (S y) (T x) = d * e y x)
    (hB : ∀ w x y, S (B w x y) = B (P w) (T x) (T y))
    (σ : K ≃+* K) (J : SemilinearSymmetry (V:=V) σ) (hJ : ∀ x, J (T x) = T (J x))
    (r : ℕ) (hr : 1 ≤ r) (a : K)
    (C : JordanChain T.toLinearMap a (r+1))
    (hmax : r+1 = largestJordanBlock T.toLinearMap)
    (w : A) (c : K) (hw : P w = c • w) :
    B w (C.vectors 0) (C.vectors 0) = 0 ∧
    B w (C.vectors 0) (J (C.vectors 0)) = 0 := by
  have ha : a ≠ 0 := by
    intro ha
    have he := C.relation 0
    have hz : T (C.vectors 0) = T 0 := by simpa [ha] using he
    exact C.endpoint_ne_zero (T.injective hz)
  have hb : JordanBound S.toLinearMap (r+1) := by
    apply (pairing_bounds T S e d hd hpair (r+1)).mp
    rw [hmax]
    exact largestJordanBlock_bound _
  have hσ : σ a ≠ 0 := fun h => ha (σ.injective (by simpa using h))
  exact ⟨product_endpoint_vanish B P T S hB r hr hb a a c ha ha C C w hw,
    product_endpoint_vanish B P T S hB r hr hb a (σ a) c ha hσ C
      (conjugateChain σ J T.toLinearMap a (r+1) hJ C) w hw⟩

end JordanSize
