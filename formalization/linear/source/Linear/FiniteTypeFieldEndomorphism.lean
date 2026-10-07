module
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.RingHom.EssFiniteType
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- A finite-transcendence-degree field is algebraic over the actual
image of each base-field endomorphism. -/
theorem fieldEndomorphism_range_isAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FinTrdeg K L]
    (φ : L →ₐ[K] L) : Algebra.IsAlgebraic φ.fieldRange L := by
  have he : Algebra.trdeg K φ.fieldRange = Algebra.trdeg K L :=
    φ.equivFieldRange.trdeg_eq.symm
  have ht := trdeg_add_eq K φ.fieldRange (A := L)
  rw [he] at ht
  have hz : Algebra.trdeg φ.fieldRange L = 0 :=
    (Cardinal.add_right_inj_of_lt_aleph0 (trdeg_lt_aleph0 K L)).mp
      (by simpa [add_comm] using ht)
  exact trdeg_eq_zero_iff.mp hz

/-- Essential finite type upgrades this actual algebraic image extension
to a finite extension. -/
theorem fieldEndomorphism_range_finite
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    (φ : L →ₐ[K] L) : Module.Finite φ.fieldRange L := by
  letI : Algebra.IsAlgebraic φ.fieldRange L := fieldEndomorphism_range_isAlgebraic φ
  letI : Algebra.EssFiniteType φ.fieldRange L := Algebra.EssFiniteType.of_comp K φ.fieldRange L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- In characteristic zero the actual image extension is formally
unramified, rather than taking generic separability as a new input. -/
theorem fieldEndomorphism_range_formallyUnramified
    {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L] [FinTrdeg K L]
    (φ : L →ₐ[K] L) : Algebra.FormallyUnramified φ.fieldRange L := by
  letI : Algebra.IsAlgebraic φ.fieldRange L := fieldEndomorphism_range_isAlgebraic φ
  exact Algebra.FormallyUnramified.of_isSeparable _ _

end LinearStudy
