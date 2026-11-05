module

public import Linear.PairingMatrix
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Perfect multiplication pairings from a cyclic socle

This supplies the finite-dimensional closed-fiber step in the relative
Jacobian proof. The one-dimensional socle is an explicit hypothesis: its
existence and its identification with the multivariable Jacobian remain
separate obligations. No perfect-pairing hypothesis is used here.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

variable {A : Type*} [CommRing A]

/-- Every nonzero ideal meets the annihilator of a nilpotent ideal. -/
theorem nonzero_ideal_meets_nilpotent_annihilator
    (N I : Ideal A) (hN : IsNilpotent N) (hI : I ≠ ⊥) :
    ∃ x : A, x ∈ I ∧ x ≠ 0 ∧ x ∈ N.annihilator := by
  classical
  have hex : ∃ n : ℕ, N ^ n * I = ⊥ := by
    obtain ⟨n, hn⟩ := hN
    exact ⟨n, by rw [hn]; simp⟩
  let n := Nat.find hex
  have hn : N ^ n * I = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    have : I = ⊥ := by simpa [h] using hn
    exact hI this
  have hprev : N ^ (n - 1) * I ≠ ⊥ :=
    Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hn0) (by decide))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
  refine ⟨x, Ideal.mul_le_right hx, hx0, ?_⟩
  apply Submodule.mem_annihilator.mpr
  intro y hy
  have hp : N * (N ^ (n - 1) * I) = ⊥ := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
    exact hn
  have hxy := Ideal.mul_mem_mul hy hx
  rw [hp] at hxy
  simpa [smul_eq_mul, mul_comm] using hxy

/-- In a local Artinian ring the preceding intersection is with its socle. -/
theorem nonzero_ideal_meets_socle [IsArtinianRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x : A, x ∈ I ∧ x ≠ 0 ∧
      x ∈ (IsLocalRing.maximalIdeal A).annihilator := by
  apply nonzero_ideal_meets_nilpotent_annihilator _ I _ hI
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at h

variable {K : Type*} [Field K] [Algebra K A]

/-- A functional nonzero on a scalar socle generator detects every nonzero
principal ideal; therefore its multiplication pairing has zero left kernel. -/
theorem socle_functional_detects_nonzero [IsArtinianRing A] [IsLocalRing A]
    (delta : A)
    (hsoc : ∀ x : A, x ∈ (IsLocalRing.maximalIdeal A).annihilator →
      ∃ b : K, x = b • delta)
    (ell : A →ₗ[K] K) (hell : ell delta ≠ 0)
    {x : A} (hx : x ≠ 0) : ∃ a : A, ell (x * a) ≠ 0 := by
  have hI : Ideal.span ({x} : Set A) ≠ ⊥ := by
    intro h
    have hm := Ideal.subset_span (Set.mem_singleton x)
    rw [h] at hm
    exact hx hm
  obtain ⟨y, hy, hy0, hys⟩ := nonzero_ideal_meets_socle _ hI
  obtain ⟨b, hb⟩ := hsoc y hys
  have hb0 : b ≠ 0 := by
    intro h
    exact hy0 (by simpa [h] using hb)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨a, ?_⟩
  have hell_y : ell y ≠ 0 := by
    rw [hb, map_smul, smul_eq_mul]
    exact mul_ne_zero hb0 hell
  simpa [ha] using hell_y

/-- The multiplication-to-dual map is injective, rather than assuming its
invertibility as a structure field. -/
theorem socle_multiplicationToDual_injective [IsArtinianRing A] [IsLocalRing A]
    (delta : A)
    (hsoc : ∀ x : A, x ∈ (IsLocalRing.maximalIdeal A).annihilator →
      ∃ b : K, x = b • delta)
    (ell : A →ₗ[K] K) (hell : ell delta ≠ 0) :
    Function.Injective (multiplicationToDual ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hx0
  obtain ⟨a, ha⟩ := socle_functional_detects_nonzero delta hsoc ell hell hx0
  exact ha (congrArg (fun f : A →ₗ[K] K => f a) hx)

/-- Construct the perfect pairing over a field from the scalar socle
generation statement and a functional nonzero on its generator. -/
def perfectPairingOfSocle [IsArtinianRing A] [IsLocalRing A]
    [FiniteDimensional K A] (delta : A)
    (hsoc : ∀ x : A, x ∈ (IsLocalRing.maximalIdeal A).annihilator →
      ∃ b : K, x = b • delta)
    (ell : A →ₗ[K] K) (hell : ell delta ≠ 0) :
    PerfectMultiplicationPairing (B := K) (A := A) where
  functional := ell
  equiv := LinearEquiv.ofInjectiveOfFinrankEq (multiplicationToDual ell)
    (socle_multiplicationToDual_injective delta hsoc ell hell)
    (Subspace.dual_finrank_eq.symm)
  equiv_apply := by intro x a; rfl

/-- Choose the functional by ordinary vector-space duality. The only socle
input is scalar generation by a nonzero element. -/
theorem exists_perfectPairing_of_scalar_socle [IsArtinianRing A] [IsLocalRing A]
    [FiniteDimensional K A] (delta : A) (hdelta : delta ≠ 0)
    (hsoc : ∀ x : A, x ∈ (IsLocalRing.maximalIdeal A).annihilator →
      ∃ b : K, x = b • delta) :
    ∃ p : PerfectMultiplicationPairing (B := K) (A := A),
      p.functional delta = 1 := by
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one K hdelta
  exact ⟨perfectPairingOfSocle delta hsoc ell (by rw [hell]; exact one_ne_zero), hell⟩

end LinearStudy
