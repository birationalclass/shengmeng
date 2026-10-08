module
public import Linear.ProjectiveSimultaneousWholePointFibers
public import Linear.ProjectiveSectionDefiningForms
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Lattice
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Count the actual inverse image of a finite target set by its actual
point fibers. The fibers are not supplied as a new, unrelated point family. -/
theorem finite_target_preimage_card {A B : Type*} (f : A → B) (Z : Set B)
    (d e : ℕ) (hd : 0 < d) (hZ : Nat.card Z=d)
    (hfib : ∀ z ∈ Z, (f ⁻¹' {z}).Finite ∧ Nat.card (f ⁻¹' {z})=e) :
    (f ⁻¹' Z).Finite ∧ Nat.card (f ⁻¹' Z)=d*e := by
  classical
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype Z := Fintype.ofFinite Z
  letI (z : Z) : Finite (f ⁻¹' {z.val}) := (hfib z.val z.property).1
  have hfin := (Set.toFinite Z).preimage' (fun z hz => (hfib z hz).1)
  refine ⟨hfin,?_⟩
  let E : (Σ z : Z, (f ⁻¹' {z.val})) ≃ (f ⁻¹' Z) :=
    Equiv.sigmaSubtypeFiberEquivSubtype f (fun _ => Iff.rfl)
  rw [← Nat.card_congr E, Nat.card_sigma]
  simp_rw [fun z : Z => (hfib z.val z.property).2]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hZ]

/-- Enumerate the actual degree-d section by d distinct target points,
with the original whole fibers, their disjoint union, and its exact size. -/
theorem finite_target_fiber_enumeration {A B : Type*} (f : A → B) (Z : Set B)
    (d e : ℕ) (hd : 0 < d) (hZ : Nat.card Z=d)
    (hfib : ∀ z ∈ Z, (f ⁻¹' {z}).Finite ∧ Nat.card (f ⁻¹' {z})=e) :
    ∃ y : Fin d → B, Function.Injective y ∧ Set.range y=Z ∧
      (∀ i, (f ⁻¹' {y i}).Finite ∧ Nat.card (f ⁻¹' {y i})=e) ∧
      (∀ i j, i ≠ j → Disjoint (f ⁻¹' {y i}) (f ⁻¹' {y j})) ∧
      (⋃ i, f ⁻¹' {y i})=f ⁻¹' Z ∧
      (f ⁻¹' Z).Finite ∧ Nat.card (f ⁻¹' Z)=d*e := by
  classical
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype Z := Fintype.ofFinite Z
  let E : Z ≃ Fin d := Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])
  let y : Fin d → B := fun i => (E.symm i).val
  have hyinj : Function.Injective y := fun i j h => E.symm.injective (Subtype.ext h)
  have hyrange : Set.range y=Z := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      exact (E.symm i).property
    · intro hz
      exact ⟨E ⟨z,hz⟩, by simp [y]⟩
  refine ⟨y,hyinj,hyrange,fun i => hfib _ (E.symm i).property,?_,?_,?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact hij (hyinj (hxi.symm.trans hxj))
  · ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hyrange]
    exact ⟨fun ⟨i,hi⟩ => ⟨i,hi.symm⟩, fun ⟨i,hi⟩ => ⟨i,hi.symm⟩⟩
  · exact finite_target_preimage_card f Z d e hd hZ hfib

end LinearStudy
