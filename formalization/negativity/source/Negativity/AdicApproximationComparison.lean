module

public import Negativity.AffineFormalFunctions
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Compatible elements of an actual inverse system of commutative rings. -/
def compatibleRingElements (B : ℕ → Type v) [∀ n, CommRing (B n)]
    (t : ∀ {m n : ℕ}, m ≤ n → (B n →+* B m)) : Subring (∀ n, B n) where
  carrier := {a | ∀ m n (h : m ≤ n), t h (a n) = a m}
  zero_mem' := by intro m n h; exact map_zero _
  one_mem' := by intro m n h; exact map_one _
  add_mem' := by
    intro a b ha hb m n h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (ha m n h) (hb m n h))
  mul_mem' := by
    intro a b ha hb m n h
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (ha m n h) (hb m n h))
  neg_mem' := by
    intro a ha m n h
    exact (map_neg _ _).trans (congrArg Neg.neg (ha m n h))

variable {R : Type u} [CommRing R] (I : Ideal R)
    (B : ℕ → Type v) [∀ n, CommRing (B n)]
    (t : ∀ {m n : ℕ}, m ≤ n → (B n →+* B m))
    (q : ∀ n, (R ⧸ I ^ (n + 1)) →+* B n)
    (htq : ∀ {m n : ℕ} (h : m ≤ n) (a : R ⧸ I ^ (n + 1)),
      t h (q n a) = q m (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) a))

/-- The canonical map, constructed from the compatible quotient maps. -/
def adicApproximationComparison :
    AdicCompletion I R →+* compatibleRingElements B t where
  toFun a := ⟨fun n => q n (AdicCompletion.evalₐ I (n + 1) a), by
    intro m n h
    rw [htq h, adic_completion_power_eval_transition I (Nat.add_le_add_right h 1)]⟩
  map_one' := by apply Subtype.ext; funext n; simp
  map_mul' a b := by apply Subtype.ext; funext n; simp
  map_zero' := by apply Subtype.ext; funext n; simp
  map_add' a b := by apply Subtype.ext; funext n; simp

/-- Final algebraic theorem: a uniform bound on the quotient-map kernels
and eventual image lifting prove bijectivity of the constructed completion
comparison. In a proper formal-functions application these two bounds
must still be proved for the actual section system; they are explicit
hypotheses here, not assertions of the geometric theorem. -/
theorem adic_comparison_bijective_of_uniform_approximation
    (c : ℕ)
    (hker : ∀ n (r : R), q (n + c) (Ideal.Quotient.mk _ r) = 0 → r ∈ I ^ (n + 1))
    (himage : ∀ n (b : B (n + c)), ∃ r : R,
      q n (Ideal.Quotient.mk _ r) = t (Nat.le_add_right n c) b) :
    Function.Bijective (adicApproximationComparison I B t q htq) := by
  classical
  let P := adicApproximationComparison I B t q htq
  constructor
  · intro a b hab
    have hz : P (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have he : ∀ n, q n (AdicCompletion.evalₐ I (n + 1) (a - b)) = 0 := by
      intro n
      exact congrArg (fun x : compatibleRingElements B t => x.1 n) hz
    have hab0 : a - b = 0 := by
      apply AdicCompletion.ext_evalₐ
      intro n
      cases n with
      | zero =>
        have : Subsingleton (R ⧸ I ^ 0) := by simp [pow_zero]
        exact Subsingleton.elim _ _
      | succ n =>
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
          (AdicCompletion.evalₐ I (n + c + 1) (a - b))
        have hk : r ∈ I ^ (n + 1) := hker n r (by rw [hr]; exact he (n + c))
        have hp := adic_completion_power_eval_transition I
          (show n + 1 ≤ n + c + 1 by omega) (a - b)
        rw [← hr] at hp
        change Ideal.Quotient.mk (I ^ (n + 1)) r =
          AdicCompletion.evalₐ I (n + 1) (a - b) at hp
        rw [← hp, map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
    exact sub_eq_zero.mp hab0
  · intro a
    have hlift : ∀ n, ∃ r : R, q (n + c) (Ideal.Quotient.mk _ r) = a.1 (n + c) := by
      intro n
      obtain ⟨r, hr⟩ := himage (n + c) (a.1 (n + c + c))
      exact ⟨r, hr.trans (a.2 (n + c) (n + c + c) (Nat.le_add_right _ c))⟩
    choose r hr using hlift
    have hrestrict : ∀ m n (h : m ≤ n),
        q (m + c) (Ideal.Quotient.mk _ (r n)) = a.1 (m + c) := by
      intro m n h
      have hs := htq (Nat.add_le_add_right h c) (Ideal.Quotient.mk _ (r n))
      change t (Nat.add_le_add_right h c) (q (n + c) (Ideal.Quotient.mk _ (r n))) =
        q (m + c) (Ideal.Quotient.mk _ (r n)) at hs
      rw [hr n, a.2 (m + c) (n + c) (Nat.add_le_add_right h c)] at hs
      exact hs.symm
    have hcongr : ∀ m n (h : m ≤ n),
        Ideal.Quotient.mk (I ^ (m + 1)) (r n) =
          Ideal.Quotient.mk (I ^ (m + 1)) (r m) := by
      intro m n h
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      apply hker m (r n - r m)
      rw [map_sub, map_sub, hrestrict m n h, hr m, sub_self]
    let z (n : ℕ) : R ⧸ (I ^ n • ⊤ : Ideal R) := match n with
      | 0 => 0
      | n + 1 => (completionPowerQuotientEquiv I (n + 1)).symm
          (Ideal.Quotient.mk _ (r n))
    have hz {m n : ℕ} (h : m ≤ n) :
        AdicCompletion.transitionMap I R h (z n) = z m := by
      cases m with
      | zero =>
        have : Subsingleton (R ⧸ (I ^ 0 • ⊤ : Ideal R)) := by simp [pow_zero]
        exact Subsingleton.elim _ _
      | succ m =>
        cases n with
        | zero => omega
        | succ n =>
          apply (completionPowerQuotientEquiv I (m + 1)).injective
          rw [completion_power_quotient_transition I h]
          simp only [z, RingEquiv.apply_symm_apply]
          change Ideal.Quotient.mk (I ^ (m + 1)) (r n) =
            Ideal.Quotient.mk (I ^ (m + 1)) (r m)
          exact hcongr m n (Nat.succ_le_succ_iff.mp h)
    let b : AdicCompletion I R := ⟨z, hz⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext n
    have heval : AdicCompletion.evalₐ I (n + 1) b = Ideal.Quotient.mk _ (r n) := by
      rw [← completion_power_quotient_eval]
      exact (completionPowerQuotientEquiv I (n + 1)).apply_symm_apply _
    change q n (AdicCompletion.evalₐ I (n + 1) b) = a.1 n
    rw [heval]
    have hs := htq (Nat.le_add_right n c) (Ideal.Quotient.mk _ (r n))
    change t (Nat.le_add_right n c) (q (n + c) (Ideal.Quotient.mk _ (r n))) =
      q n (Ideal.Quotient.mk _ (r n)) at hs
    rw [hr n, a.2 n (n + c) (Nat.le_add_right n c)] at hs
    exact hs.symm

end
end Negativity
