module

public import Negativity.AffineThickeningSections
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Identify the module-quotient convention in mathlib's actual adic
completion with the ordinary ideal-power quotient. -/
def completionPowerQuotientEquiv {R : Type*} [CommRing R] (K : Ideal R) (n : ℕ) :
    R ⧸ (K ^ n • ⊤ : Ideal R) ≃+* R ⧸ K ^ n :=
  (Ideal.quotientEquivAlgOfEq R (show (K ^ n • ⊤ : Ideal R) = K ^ n from by
    ext x; simp)).toRingEquiv

theorem completion_power_quotient_eval {R : Type*} [CommRing R]
    (K : Ideal R) (n : ℕ) (a : AdicCompletion K R) :
    completionPowerQuotientEquiv K n (a.1 n) = AdicCompletion.evalₐ K n a := rfl

theorem completion_power_quotient_transition {R : Type*} [CommRing R]
    (K : Ideal R) {m n : ℕ} (h : m ≤ n) (a : R ⧸ (K ^ n • ⊤ : Ideal R)) :
    completionPowerQuotientEquiv K m (AdicCompletion.transitionMap K R h a) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
        (completionPowerQuotientEquiv K n a) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

theorem adic_completion_power_eval_transition {R : Type*} [CommRing R]
    (K : Ideal R) {m n : ℕ} (h : m ≤ n) (a : AdicCompletion K R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ K n a) =
      AdicCompletion.evalₐ K m a := by
  rw [← completion_power_quotient_eval, ← completion_power_quotient_eval,
    ← completion_power_quotient_transition K h, a.2 h]

/-- The actual completion-to-thickening-functions comparison for an
affine scheme, built from the actual quotient comparisons. -/
def actualAffineFormalFunctionsMap (X : Scheme.{u}) [IsAffine X]
    (I : X.IdealSheafData) :
    AdicCompletion (I.ideal ⟨⊤, isAffineOpen_top X⟩) Γ(X, ⊤) →+*
      actualInfinitesimalSections I where
  toFun a := ⟨fun n => (actualAffineThickeningSectionsEquiv X I n).symm
    (AdicCompletion.evalₐ _ (n + 1) a), by
      intro m n h
      apply (actualAffineThickeningSectionsEquiv X I m).injective
      rw [actual_affine_thickening_sections_transition]
      simp only [RingEquiv.apply_symm_apply]
      exact adic_completion_power_eval_transition _ (Nat.add_le_add_right h 1) a⟩
  map_one' := by apply Subtype.ext; funext n; simp
  map_mul' a b := by apply Subtype.ext; funext n; simp
  map_zero' := by apply Subtype.ext; funext n; simp
  map_add' a b := by apply Subtype.ext; funext n; simp

/-- Final theorem: for an actual affine scheme, the canonical comparison
between its actual completed section ring and the actual inverse limit
of regular functions on all actual ideal-power thickenings is bijective.
No abstract comparison map or compatibility hypothesis is supplied.
The proper nonaffine formal-functions theorem needed for birational
fiber connectedness is a separate remaining geometric theorem. -/
theorem actual_affine_formal_functions_bijective (X : Scheme.{u}) [IsAffine X]
    (I : X.IdealSheafData) : Function.Bijective (actualAffineFormalFunctionsMap X I) := by
  classical
  let K := I.ideal ⟨⊤, isAffineOpen_top X⟩
  constructor
  · intro a b hab
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
      have : Subsingleton (Γ(X, ⊤) ⧸ K ^ 0) := by simp [pow_zero]
      exact Subsingleton.elim _ _
    | succ n =>
      have h := congrArg (fun c : actualInfinitesimalSections I =>
        actualAffineThickeningSectionsEquiv X I n (c.1 n)) hab
      simpa [actualAffineFormalFunctionsMap] using h
  · intro a
    let v (n : ℕ) : Γ(X, ⊤) ⧸ (K ^ n • ⊤ : Ideal Γ(X, ⊤)) := match n with
      | 0 => 0
      | n + 1 => (completionPowerQuotientEquiv K (n + 1)).symm
          (actualAffineThickeningSectionsEquiv X I n (a.1 n))
    have hv {m n : ℕ} (h : m ≤ n) : AdicCompletion.transitionMap K Γ(X, ⊤) h (v n) = v m := by
      cases m with
      | zero =>
        have : Subsingleton (Γ(X, ⊤) ⧸ (K ^ 0 • ⊤ : Ideal Γ(X, ⊤))) := by
          simp [pow_zero]
        exact Subsingleton.elim _ _
      | succ m =>
        cases n with
        | zero => omega
        | succ n =>
          apply (completionPowerQuotientEquiv K (m + 1)).injective
          rw [completion_power_quotient_transition]
          simp only [v, RingEquiv.apply_symm_apply]
          have ht := actual_affine_thickening_sections_transition X I
            (Nat.succ_le_succ_iff.mp h) (a.1 n)
          rw [a.2 m n (Nat.succ_le_succ_iff.mp h)] at ht
          exact ht.symm
    let b : AdicCompletion K Γ(X, ⊤) := ⟨v, hv⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext n
    apply (actualAffineThickeningSectionsEquiv X I n).injective
    change (actualAffineThickeningSectionsEquiv X I n)
      ((actualAffineThickeningSectionsEquiv X I n).symm
        (AdicCompletion.evalₐ K (n + 1) b)) = _
    rw [RingEquiv.apply_symm_apply]
    rw [← completion_power_quotient_eval]
    exact (completionPowerQuotientEquiv K (n + 1)).apply_symm_apply _

end
end Negativity
