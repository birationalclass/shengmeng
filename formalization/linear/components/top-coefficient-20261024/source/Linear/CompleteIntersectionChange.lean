module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Linear.Reduction
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

def equationChangeQuotientEquiv {ι : Type*} (e : R ≃ₐ[B] R) (H : ι → R) :
    (R ⧸ Ideal.span (Set.range H)) ≃ₐ[B]
      (R ⧸ Ideal.span (Set.range (fun i => e (H i)))) :=
  Ideal.quotientEquivAlg _ _ e (by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨H i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩)

theorem equationChangeQuotientEquiv_mk {ι : Type*} (e : R ≃ₐ[B] R) (H : ι → R) (x : R) :
    equationChangeQuotientEquiv e H (Ideal.Quotient.mk (Ideal.span (Set.range H)) x) =
      Ideal.Quotient.mk (Ideal.span (Set.range (fun i => e (H i)))) (e x) := by
  rfl

theorem regularSequence_change_equations (e : R ≃ₐ[B] R) (H : List R) :
    RingTheory.Sequence.IsRegular R H ↔ RingTheory.Sequence.IsRegular R (H.map e) := by
  apply e.toAddEquiv.isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r hr x
  exact e.map_mul r x

theorem equationChangeQuotient_finite {ι : Type*} (e : R ≃ₐ[B] R) (H : ι → R)
    [Module.Finite B (R ⧸ Ideal.span (Set.range H))] :
    Module.Finite B (R ⧸ Ideal.span (Set.range (fun i => e (H i)))) :=
  Module.Finite.equiv (equationChangeQuotientEquiv e H).toLinearEquiv

theorem equationChangeQuotient_flat {ι : Type*} (e : R ≃ₐ[B] R) (H : ι → R)
    [Module.Flat B (R ⧸ Ideal.span (Set.range H))] :
    Module.Flat B (R ⧸ Ideal.span (Set.range (fun i => e (H i)))) :=
  Module.Flat.of_linearEquiv (equationChangeQuotientEquiv e H).toLinearEquiv.symm

theorem nilradical_kernel_transport {A C : Type*} [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C] (e : C ≃ₐ[B] A) (q : A →ₐ[B] B)
    (hq : RingHom.ker q.toRingHom = nilradical A) :
    RingHom.ker (q.comp e.toAlgHom).toRingHom = nilradical C := by
  ext x
  rw [RingHom.mem_ker, mem_nilradical]
  change q (e x) = 0 ↔ IsNilpotent x
  have h : q (e x) = 0 ↔ IsNilpotent (e x) := by
    rw [← mem_nilradical, ← hq, RingHom.mem_ker]
    rfl
  rw [h]
  constructor
  · intro hx
    simpa only [AlgEquiv.symm_apply_apply] using hx.map e.symm
  · intro hx
    exact hx.map e
end LinearStudy
