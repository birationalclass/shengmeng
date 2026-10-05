module

public import Linear.Duality
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# From a primitive annihilator element to the specified generator

This closes the local-ring/Nakayama coefficient step, given a perfect pairing
and a kernel-annihilating element surviving the closed fiber. It does not prove
that the Jacobian is such an element: that is the still-open SS input.
-/

@[expose] public section

namespace LinearStudy

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- The predicate in the preceding files is exactly membership in the standard
ideal annihilator from mathlib. -/
theorem annihilates_iff_mem_annihilator (N : Ideal A) (x : A) :
    Annihilates N x ↔ x ∈ N.annihilator := by
  simp only [Annihilates, Submodule.mem_annihilator, smul_eq_mul, mul_comm]

/-- An actual equality with the nilradical's annihilator, under pairing input. -/
theorem nilradical_annihilator_scalar_generation
    (q : A →ₐ[B] B) (hq : RingHom.ker q.toRingHom = nilradical A)
    (p : PerfectMultiplicationPairing (B := B) (A := A)) (x : A) :
    x ∈ (nilradical A).annihilator ↔ ∃ b : B, x = b • dualGenerator q p := by
  rw [← annihilates_iff_mem_annihilator, ← hq]
  exact annihilator_iff_scalar_multiple q p x

/-- Every kernel-annihilating element with unit scalar coefficient generates
the same annihilator. -/
theorem unit_coefficient_generates_annihilator
    (q : A →ₐ[B] B) (p : PerfectMultiplicationPairing (B := B) (A := A))
    (delta : A) (hd : Annihilates (RingHom.ker q.toRingHom) delta)
    (hu : IsUnit (p.functional delta)) (x : A) :
    Annihilates (RingHom.ker q.toRingHom) x ↔ ∃ b : B, x = b • delta := by
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := hu
    have hd' := annihilator_eq_scalar_generator q p hd
    refine ⟨p.functional x * (↑(u⁻¹) : B), ?_⟩
    calc
      x = p.functional x • dualGenerator q p := annihilator_eq_scalar_generator q p hx
      _ = (p.functional x * (↑(u⁻¹) : B)) • delta := by
        rw [hd']
        simp only [← mul_smul, ← hu, mul_assoc, Units.inv_mul, mul_one]
  · rintro ⟨b, rfl⟩
    exact scalar_multiple_annihilates _ hd b

/-- Over a local base, survival modulo m_B A forces the generator coefficient
to be a unit. -/
theorem primitive_annihilator_coefficient_isUnit [IsLocalRing B]
    (q : A →ₐ[B] B) (p : PerfectMultiplicationPairing (B := B) (A := A))
    (delta : A) (hd : Annihilates (RingHom.ker q.toRingHom) delta)
    (hprimitive : delta ∉ IsLocalRing.maximalIdeal B • (⊤ : Submodule B A)) :
    IsUnit (p.functional delta) := by
  by_contra hu
  have hm : p.functional delta ∈ IsLocalRing.maximalIdeal B := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hu
  apply hprimitive
  rw [annihilator_eq_scalar_generator q p hd]
  exact Submodule.smul_mem_smul hm (Submodule.mem_top)

/-- The primitive-generator portion of Lemma 3.1, isolated from the still-open
complete-intersection and Jacobian constructions. -/
theorem primitive_annihilator_generates [IsLocalRing B]
    (q : A →ₐ[B] B) (p : PerfectMultiplicationPairing (B := B) (A := A))
    (delta : A) (hd : Annihilates (RingHom.ker q.toRingHom) delta)
    (hprimitive : delta ∉ IsLocalRing.maximalIdeal B • (⊤ : Submodule B A))
    (x : A) :
    Annihilates (RingHom.ker q.toRingHom) x ↔ ∃ b : B, x = b • delta :=
  unit_coefficient_generates_annihilator q p delta hd
    (primitive_annihilator_coefficient_isUnit q p delta hd hprimitive) x

end LinearStudy
