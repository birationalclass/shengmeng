module

public import Linear.Duality
public import Linear.Primitive
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The trace element for a nilpotent thickening of the base

This identifies the algebraic trace functional and its dual element in
general, without assuming the Jacobian is the trace element. The latter
comparison is the separate complete-intersection residue/trace obligation.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- The element dual to the actual algebraic trace under a given pairing. -/
def traceElement (p : PerfectMultiplicationPairing (B := B) (A := A)) : A :=
  p.equiv.symm (Algebra.trace B A)

@[simp] theorem traceElement_pairing
    (p : PerfectMultiplicationPairing (B := B) (A := A)) (a : A) :
    p.functional (traceElement p * a) = Algebra.trace B A a := by
  rw [← p.equiv_apply]
  change p.equiv (p.equiv.symm (Algebra.trace B A)) a = Algebra.trace B A a
  rw [p.equiv.apply_symm_apply]

/-- Over a reduced base the trace of an element with nilpotent reduction
kernel is its reduction times the module rank. -/
theorem trace_eq_rank_smul_reduction [IsReduced B] [StrongRankCondition B]
    [Module.Free B A] (q : A →ₐ[B] B)
    (hq : RingHom.ker q.toRingHom = nilradical A) (a : A) :
    Algebra.trace B A a = Module.finrank B A • q a := by
  have hker : a - algebraMap B A (q a) ∈ RingHom.ker q.toRingHom := by
    change q (a - algebraMap B A (q a)) = 0
    simp
  have hnil : IsNilpotent (a - algebraMap B A (q a)) := by
    apply mem_nilradical.mp
    rwa [← hq]
  have htrace := Algebra.isNilpotent_trace_of_isNilpotent (R := B) hnil
  have hz : Algebra.trace B A (a - algebraMap B A (q a)) = 0 :=
    isNilpotent_iff_eq_zero.mp htrace
  rw [map_sub, Algebra.trace_algebraMap] at hz
  exact sub_eq_zero.mp hz

/-- The trace element is the rank times the dual reduction generator. -/
theorem traceElement_eq_rank_dualGenerator [IsReduced B] [StrongRankCondition B]
    [Module.Free B A] (q : A →ₐ[B] B)
    (hq : RingHom.ker q.toRingHom = nilradical A)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) :
    traceElement p = Module.finrank B A • dualGenerator q p := by
  apply p.equiv.injective
  ext a
  rw [p.equiv_apply, traceElement_pairing, map_nsmul]
  change Algebra.trace B A a = Module.finrank B A • p.equiv (dualGenerator q p) a
  rw [p.equiv_apply, dualGenerator_pairing, trace_eq_rank_smul_reduction q hq]

/-- The algebraic trace element annihilates the reduction kernel. -/
theorem traceElement_annihilates_kernel [IsReduced B] [StrongRankCondition B]
    [Module.Free B A] (q : A →ₐ[B] B)
    (hq : RingHom.ker q.toRingHom = nilradical A)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) :
    Annihilates (RingHom.ker q.toRingHom) (traceElement p) := by
  rw [traceElement_eq_rank_dualGenerator q hq p]
  intro a ha
  rw [nsmul_eq_mul]
  have hz := (dualGenerator_annihilates q p) a ha
  calc
    a * ((Module.finrank B A : A) * dualGenerator q p)
        = (Module.finrank B A : A) * (a * dualGenerator q p) := by ring
    _ = 0 := by rw [hz, mul_zero]

/-- The value of the pairing functional on the trace element is its rank. -/
theorem traceElement_functional [StrongRankCondition B] [Module.Free B A]
    (p : PerfectMultiplicationPairing (B := B) (A := A)) :
    p.functional (traceElement p) = (Module.finrank B A : B) := by
  have ht := Algebra.trace_algebraMap (R := B) (S := A) (1 : B)
  simpa using (traceElement_pairing p (1 : A)).trans (by simpa using ht)

/-- Over a characteristic-zero field a nonzero finite algebra has a
nonzero trace element. This does not assert that it is the Jacobian. -/
theorem traceElement_nonzero_over_field {K : Type*} [Field K] [CharZero K]
    [Algebra K A] [FiniteDimensional K A] [Nontrivial A]
    (p : PerfectMultiplicationPairing (B := K) (A := A)) : traceElement p ≠ 0 := by
  intro h
  have hz := traceElement_functional p
  rw [h, map_zero] at hz
  have hcast : (Module.finrank K A : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos (R := K) (M := A)))
  exact hcast hz.symm

/-- If the rank is a unit, the trace element scalar-generates the
annihilator. A characteristic-zero base alone would not imply this unit
condition (for example over the integers). -/
theorem traceElement_generates_annihilator [IsReduced B] [StrongRankCondition B]
    [Module.Free B A] (q : A →ₐ[B] B)
    (hq : RingHom.ker q.toRingHom = nilradical A)
    (p : PerfectMultiplicationPairing (B := B) (A := A))
    (hrank : IsUnit (Module.finrank B A : B)) (x : A) :
    Annihilates (RingHom.ker q.toRingHom) x ↔ ∃ u : B, x = u • traceElement p := by
  apply unit_coefficient_generates_annihilator q p _
    (traceElement_annihilates_kernel q hq p)
  rwa [traceElement_functional]

/-- A residue/trace identity identifies a candidate element with the trace
element. Establishing this identity for the actual Jacobian is still open. -/
theorem eq_traceElement_of_residue_trace
    (p : PerfectMultiplicationPairing (B := B) (A := A)) (delta : A)
    (htrace : ∀ a : A, p.functional (delta * a) = Algebra.trace B A a) :
    delta = traceElement p := by
  apply p.equiv.injective
  ext a
  rw [p.equiv_apply, p.equiv_apply, htrace, traceElement_pairing]

end LinearStudy
