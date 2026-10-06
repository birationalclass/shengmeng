module

public import Linear.SoclePairing
public import Linear.Primitive
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Lifting a closed-fiber pairing over a local base

The closed fiber is the actual algebraic tensor product with the residue
field. A functional is lifted using a finite free basis, and its Gram
determinant is compared with the closed-fiber determinant. The cyclic
socle hypothesis is explicit and is not the relative Jacobian theorem.
-/

@[expose] public section
noncomputable section
namespace LinearStudy
open scoped TensorProduct

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
variable [IsLocalRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every functional on the actual residue-field tensor product lifts to
a functional on the finite free algebra. -/
theorem exists_residue_functional_lift (b : Module.Basis ι B A)
    (ellbar : Module.Dual (B ⧸ IsLocalRing.maximalIdeal B)
      ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)) :
    ∃ ell : A →ₗ[B] B,
      Module.Dual.baseChange (B ⧸ IsLocalRing.maximalIdeal B) ell = ellbar := by
  classical
  let K := B ⧸ IsLocalRing.maximalIdeal B
  let bc : Module.Basis ι K (K ⊗[B] A) := b.baseChange K
  have hsurj := Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal B)
  choose coeff hcoeff using fun i : ι => hsurj (ellbar (bc i))
  let ell : A →ₗ[B] B := b.constr B coeff
  refine ⟨ell, bc.ext fun i => ?_⟩
  simp only [bc, Module.Basis.baseChange_apply, Module.Dual.baseChange_apply_tmul]
  simpa [ell, bc, Module.Basis.baseChange_apply, Algebra.smul_def] using hcoeff i

omit [Fintype ι] [DecidableEq ι] in
/-- The multiplication Gram matrix commutes with residue-field base change. -/
theorem residue_multiplicationGram (b : Module.Basis ι B A) (ell : A →ₗ[B] B) :
    (multiplicationGram b ell).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) =
    multiplicationGram (b.baseChange (B ⧸ IsLocalRing.maximalIdeal B))
      (Module.Dual.baseChange (B ⧸ IsLocalRing.maximalIdeal B) ell) := by
  ext i j
  simp [multiplicationGram, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

/-- If the actual closed fiber has a scalar socle generator, a perfect
multiplication pairing exists over the local base itself. -/
theorem exists_relative_perfectPairing_of_residue_socle
    (b : Module.Basis ι B A)
    [IsLocalRing ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)]
    (delta : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A) (hdelta : delta ≠ 0)
    (hsoc : ∀ x : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A,
      x ∈ (IsLocalRing.maximalIdeal
        ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)).annihilator →
      ∃ u : B ⧸ IsLocalRing.maximalIdeal B, x = u • delta) :
    Nonempty (PerfectMultiplicationPairing (B := B) (A := A)) := by
  let K := B ⧸ IsLocalRing.maximalIdeal B
  let : Field K := Ideal.Quotient.field _
  let C := K ⊗[B] A
  let bc : Module.Basis ι K C := b.baseChange K
  have : Module.Finite K C := Module.Finite.of_basis bc
  have : IsArtinianRing C := IsArtinianRing.of_finite K C
  obtain ⟨pc, _⟩ := exists_perfectPairing_of_scalar_socle (K := K) delta hdelta hsoc
  obtain ⟨ell, hell⟩ := exists_residue_functional_lift b pc.functional
  have hmat : LinearMap.toMatrix bc bc.dualBasis pc.equiv =
      multiplicationGram bc pc.functional := by
    ext i j
    rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
    exact pc.equiv_apply _ _
  have hunit : IsUnit (multiplicationGram bc pc.functional).det := by
    rw [← hmat]
    exact pc.equiv.isUnit_det bc bc.dualBasis
  have hres : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
      (multiplicationGram b ell).det ≠ 0 := by
    rw [RingHom.map_det]
    change ((multiplicationGram b ell).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))).det ≠ 0
    rw [residue_multiplicationGram, hell]
    exact hunit.ne_zero
  obtain ⟨p, _⟩ := exists_perfectPairing_of_residueDet_ne_zero b ell hres
  exact ⟨p⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Finite flatness over the local base supplies the finite free basis;
the caller need not assume or choose one. -/
theorem exists_finiteFlat_pairing_of_residue_socle
    [Module.Finite B A] [Module.Flat B A]
    [IsLocalRing ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)]
    (delta : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A) (hdelta : delta ≠ 0)
    (hsoc : ∀ x : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A,
      x ∈ (IsLocalRing.maximalIdeal
        ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)).annihilator →
      ∃ u : B ⧸ IsLocalRing.maximalIdeal B, x = u • delta) :
    Nonempty (PerfectMultiplicationPairing (B := B) (A := A)) := by
  have : Module.Free B A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis B A
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex B A)
  let := Classical.decEq (Module.Free.ChooseBasisIndex B A)
  exact exists_relative_perfectPairing_of_residue_socle b delta hdelta hsoc

omit [Fintype ι] [DecidableEq ι] in
/-- Nonzero reduction to the actual tensor-product fiber is the primitive
condition needed in the annihilator coefficient argument. -/
theorem primitive_of_residue_tensor_nonzero (delta : A)
    (hdelta : (1 ⊗ₜ[B] delta : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A) ≠ 0) :
    delta ∉ IsLocalRing.maximalIdeal B • (⊤ : Submodule B A) := by
  intro h
  apply hdelta
  let e := TensorProduct.quotTensorEquivQuotSMul A (IsLocalRing.maximalIdeal B)
  apply e.injective
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

omit [Fintype ι] [DecidableEq ι] in
/-- Assemble the relative annihilator argument without assuming a perfect
pairing. The unproved Jacobian inputs are stated precisely: annihilation,
nonzero closed-fiber image, and scalar closed-fiber socle generation. -/
theorem finiteFlat_annihilator_from_closed_socle
    [Module.Finite B A] [Module.Flat B A]
    [IsLocalRing ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)]
    (q : A →ₐ[B] B) (delta : A)
    (hd : Annihilates (RingHom.ker q.toRingHom) delta)
    (hdelta : (1 ⊗ₜ[B] delta : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A) ≠ 0)
    (hsoc : ∀ x : (B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A,
      x ∈ (IsLocalRing.maximalIdeal
        ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] A)).annihilator →
      ∃ u : B ⧸ IsLocalRing.maximalIdeal B, x = u • (1 ⊗ₜ[B] delta))
    (x : A) :
    Annihilates (RingHom.ker q.toRingHom) x ↔ ∃ u : B, x = u • delta := by
  obtain ⟨p⟩ := exists_finiteFlat_pairing_of_residue_socle _ hdelta hsoc
  exact primitive_annihilator_generates q p delta hd
    (primitive_of_residue_tensor_nonzero delta hdelta) x

end LinearStudy
