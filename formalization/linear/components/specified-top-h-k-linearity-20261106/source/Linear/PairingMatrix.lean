module

public import Linear.Duality
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Constructing the perfect pairing by a determinant criterion

A finite basis and a functional whose multiplication Gram determinant is a
unit suffice to construct the perfect pairing. Over a local base, nonzero
reduction of this determinant suffices. Existence of such a functional on a
complete-intersection closed fiber still needs the Gorenstein theorem.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- Multiplication followed by a given functional, as a map to the dual. -/
def multiplicationToDual (ell : A →ₗ[B] B) : A →ₗ[B] (A →ₗ[B] B) where
  toFun x :=
    { toFun a := ell (x * a)
      map_add' a b := by simp [mul_add]
      map_smul' b a := by simp }
  map_add' x y := by ext a; simp [add_mul]
  map_smul' b x := by ext a; simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Row i and column j are the pairing of the two indicated basis elements. -/
def multiplicationGram (b : Module.Basis ι B A) (ell : A →ₗ[B] B) : Matrix ι ι B :=
  fun i j => ell (b j * b i)

theorem multiplicationToDual_matrix (b : Module.Basis ι B A) (ell : A →ₗ[B] B) :
    LinearMap.toMatrix b b.dualBasis (multiplicationToDual ell) =
      multiplicationGram b ell := by
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
  rfl

/-- Construct the inverse by the actual Gram matrix inverse. -/
def perfectPairingOfUnitDet (b : Module.Basis ι B A) (ell : A →ₗ[B] B)
    (hu : IsUnit (multiplicationGram b ell).det) :
    PerfectMultiplicationPairing (B := B) (A := A) where
  functional := ell
  equiv := LinearEquiv.ofIsUnitDet (f := multiplicationToDual ell) (v := b)
    (v' := b.dualBasis) (by
    rw [multiplicationToDual_matrix]
    exact hu)
  equiv_apply := by intro x a; rfl

/-- The determinant/Nakayama lift step for a local base. This takes a finite
basis and a suitable functional; it does not assume a perfect-pairing structure. -/
theorem exists_perfectPairing_of_residueDet_ne_zero [IsLocalRing B]
    (b : Module.Basis ι B A) (ell : A →ₗ[B] B)
    (hres : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
      (multiplicationGram b ell).det ≠ 0) :
    ∃ p : PerfectMultiplicationPairing (B := B) (A := A), p.functional = ell := by
  have hu : IsUnit (multiplicationGram b ell).det := by
    have hm : (multiplicationGram b ell).det ∉ IsLocalRing.maximalIdeal B := by
      intro hm
      exact hres (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hm
  exact ⟨perfectPairingOfUnitDet b ell hu, rfl⟩

end LinearStudy
