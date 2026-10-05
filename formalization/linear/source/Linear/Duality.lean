module

public import Linear.Reduction
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Ring

/-!
# Annihilators from a perfect multiplication pairing

This is an actual ring-theoretic theorem. The existence of the perfect pairing
for a finite flat complete intersection is an explicit input, not proved here.
-/

@[expose] public section

namespace LinearStudy

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- A perfect B-linear multiplication pairing on A. -/
structure PerfectMultiplicationPairing where
  functional : A →ₗ[B] B
  equiv : A ≃ₗ[B] (A →ₗ[B] B)
  equiv_apply : ∀ x a, equiv x a = functional (x * a)

/-- The element corresponding under duality to the reduction map. -/
noncomputable def dualGenerator (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) : A :=
  p.equiv.symm q.toLinearMap

@[simp] theorem dualGenerator_pairing (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) (a : A) :
    p.functional (dualGenerator q p * a) = q a := by
  rw [← p.equiv_apply]
  change p.equiv (p.equiv.symm q.toLinearMap) a = q a
  rw [p.equiv.apply_symm_apply]
  rfl

@[simp] theorem dualGenerator_functional (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) :
    p.functional (dualGenerator q p) = 1 := by
  simpa using dualGenerator_pairing q p (1 : A)

/-- The dual generator is annihilated by the kernel of the reduction map. -/
theorem dualGenerator_annihilates (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) :
    Annihilates (RingHom.ker q.toRingHom) (dualGenerator q p) := by
  intro n hn
  apply p.equiv.injective
  rw [map_zero]
  ext a
  change p.equiv (n * dualGenerator q p) a = 0
  rw [p.equiv_apply]
  have hn' : q n = 0 := hn
  calc
    p.functional (n * dualGenerator q p * a)
        = p.functional (dualGenerator q p * (n * a)) := by congr 1; ring
    _ = q (n * a) := dualGenerator_pairing q p _
    _ = 0 := by rw [map_mul, hn', zero_mul]

/-- A kernel-annihilating element is a scalar multiple of the dual generator. -/
theorem annihilator_eq_scalar_generator (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A))
    {x : A} (hx : Annihilates (RingHom.ker q.toRingHom) x) :
    x = p.functional x • dualGenerator q p := by
  apply p.equiv.injective
  ext a
  have hn : a - algebraMap B A (q a) ∈ RingHom.ker q.toRingHom := by
    change q (a - algebraMap B A (q a)) = 0
    simp
  have hmul : a * x = algebraMap B A (q a) * x := by
    have h := hx _ hn
    simpa only [sub_mul, sub_eq_zero] using h
  calc
    p.equiv x a = p.functional (x * a) := p.equiv_apply _ _
    _ = p.functional (q a • x) := by rw [mul_comm, hmul, Algebra.smul_def]
    _ = q a * p.functional x := by rw [map_smul, smul_eq_mul]
    _ = p.functional x * q a := mul_comm _ _
    _ = p.equiv (p.functional x • dualGenerator q p) a := by
      rw [p.equiv.map_smul]
      change p.functional x * q a = p.functional x * p.equiv (dualGenerator q p) a
      rw [p.equiv_apply, dualGenerator_pairing]

/-- A precise scalar-generation statement, with perfect pairing as input. -/
theorem annihilator_iff_scalar_multiple (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) (x : A) :
    Annihilates (RingHom.ker q.toRingHom) x ↔
      ∃ b : B, x = b • dualGenerator q p := by
  constructor
  · intro hx
    exact ⟨p.functional x, annihilator_eq_scalar_generator q p hx⟩
  · rintro ⟨b, rfl⟩
    exact scalar_multiple_annihilates _ (dualGenerator_annihilates q p) b

/-- A splitting of the cyclic B-module into A; no Jacobian identification is used. -/
theorem dualGenerator_scalar_retraction (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) (b : B) :
    p.functional (b • dualGenerator q p) = b := by
  rw [map_smul, dualGenerator_functional, smul_eq_mul, mul_one]

/-- Nonzero images require a quotient argument in addition to annihilation. -/
theorem dualGenerator_quotient_nonzero (q : A →ₐ[B] B)
    (p : PerfectMultiplicationPairing (B := B) (A := A))
    (J : Ideal A) (m : Ideal B) (hm : (1 : B) ∉ m)
    (hJ : ∀ a ∈ J, p.functional a ∈ m) :
    Ideal.Quotient.mk J (dualGenerator q p) ≠ 0 := by
  rw [quotient_image_nonzero_iff]
  intro h
  have h' := hJ _ h
  rw [dualGenerator_functional] at h'
  exact hm h'

end LinearStudy
