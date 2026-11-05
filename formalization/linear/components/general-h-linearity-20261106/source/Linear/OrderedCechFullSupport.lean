module
public import Linear.OrderedCechSupportContraction
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Preorder.Finite
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry.Scheme.Modules
universe u v
variable {ι : Type v} [Fintype ι] [LinearOrder ι]

/-- The increasing tuple of every coordinate in the top degree. -/
def orderedCechFullIndex (n : ℕ) (h : Fintype.card ι = n+1) :
    OrderedCechIndex ι n :=
  ⟨monoEquivOfFin ι h,(monoEquivOfFin ι h).strictMono⟩

/-- In top degree the ordered tuple is unique. This follows from the
existing finite-order rigidity theorem, not from a supplied uniqueness input. -/
theorem orderedCechIndex_eq_full (n : ℕ) (h : Fintype.card ι = n+1)
    (a : OrderedCechIndex ι n) : a = orderedCechFullIndex n h := by
  apply Subtype.ext
  funext k
  let e := monoEquivOfFin ι h
  have hi : (e.symm ∘ a.1) = id := (e.symm.strictMono.comp a.2).eq_id
  apply e.symm.injective
  simpa [orderedCechFullIndex,e] using congrFun hi k

theorem orderedCechFullIndex_range (n : ℕ) (h : Fintype.card ι = n+1) :
    Set.range (orderedCechFullIndex n h).1 = Set.univ := by
  exact Set.range_eq_univ.mpr (monoEquivOfFin ι h).surjective

/-- With all coordinates required, lower-degree cochains are zero. -/
theorem orderedCechFullSupport_eq_zero (R : Type u) [CommRing R]
    (n : ℕ) (h : n+1 < Fintype.card ι)
    (s : OrderedCechSupportCochain R (Set.univ : Set ι) n) : s = 0 := by
  apply Subtype.ext
  funext a
  apply s.2 a
  intro ha
  have hs : Function.Surjective a.1 := fun i => ha (Set.mem_univ i)
  have hc := Fintype.card_le_of_surjective a.1 hs
  simp only [Fintype.card_fin] at hc
  omega

theorem orderedCechSupport_eq_zero_of_full_support (R : Type u) [CommRing R]
    (N : Set ι) (hN : N = Set.univ) (n : ℕ) (h : n+1 < Fintype.card ι)
    (s : OrderedCechSupportCochain R N n) : s = 0 := by
  subst N
  exact orderedCechFullSupport_eq_zero R n h s

/-- Evaluation at the sole top index detects zero for any required support. -/
theorem orderedCechSupport_top_eval_eq_zero_iff (R : Type u) [CommRing R]
    (N : Set ι) (n : ℕ) (h : Fintype.card ι = n+1)
    (s : OrderedCechSupportCochain R N n) :
    s.1 (orderedCechFullIndex n h) = 0 ↔ s = 0 := by
  constructor
  · intro hs
    apply Subtype.ext
    funext a
    rw [orderedCechIndex_eq_full n h a]
    exact hs
  · rintro rfl
    rfl

/-- Top full-support cochains are exactly one copy of the coefficient ring,
with the map given by evaluation at the actual increasing full tuple. -/
def orderedCechFullSupportEquiv (R : Type u) [CommRing R]
    (n : ℕ) (h : Fintype.card ι = n+1) :
    OrderedCechSupportCochain R (Set.univ : Set ι) n ≃ₗ[R] R where
  toFun s := s.1 (orderedCechFullIndex n h)
  invFun r := ⟨fun _ => r,fun a ha => by
    have he := orderedCechIndex_eq_full n h a
    subst a
    exact False.elim (ha (by rw [orderedCechFullIndex_range]))⟩
  left_inv s := by
    apply Subtype.ext
    funext a
    rw [orderedCechIndex_eq_full n h a]
  right_inv r := rfl
  map_add' s t := rfl
  map_smul' r s := rfl
end LinearStudy
