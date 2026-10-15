module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.Tactic
public import Linear.Iteration

/-! # Actual homogeneous coordinates and the main target
We use mathlib polynomials and projective points, not an opaque `Variety` type.
The main target is a Prop DEFINITION, not a theorem. The comparison of this
complex-point formulation with the Scheme formulation is a separate obligation.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev CoordinateVector (n : ℕ) := Fin (n + 1) → ℂ
abbrev CoordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ
abbrev ProjectivePoint (n : ℕ) := Projectivization ℂ (CoordinateVector n)

/-- Homogeneity gives the scaling law for actual polynomial evaluation. -/
theorem homogeneous_eval_smul {σ : Type*} {K : Type*} [CommSemiring K]
    {P : MvPolynomial σ K} {m : ℕ} (hP : P.IsHomogeneous m)
    (a : K) (v : σ → K) :
    MvPolynomial.eval (a • v) P = a ^ m * MvPolynomial.eval v P := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add P Q hP hQ ihP ihQ => simp [ihP, ihQ, mul_add]
  | monomial d c hd =>
    have hdeg : (∑ i ∈ d.support, d i) = m := by
      simpa [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum] using hd
    simp only [MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul,
      Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
    ring

/-- A base-point-free tuple of degree-q homogeneous forms. -/
structure HomogeneousEndomorphism (n : ℕ) where
  degree : ℕ
  forms : Fin (n + 1) → CoordinateRing n
  homogeneous : ∀ i, (forms i).IsHomogeneous degree
  noBasePoint : ∀ v : CoordinateVector n, v ≠ 0 →
    (fun i => MvPolynomial.eval v (forms i)) ≠ 0

def HomogeneousEndomorphism.evalVector {n : ℕ} (f : HomogeneousEndomorphism n)
    (v : CoordinateVector n) : CoordinateVector n :=
  fun i => MvPolynomial.eval v (f.forms i)

theorem HomogeneousEndomorphism.evalVector_smul {n : ℕ}
    (f : HomogeneousEndomorphism n) (a : ℂ) (v : CoordinateVector n) :
    f.evalVector (a • v) = a ^ f.degree • f.evalVector v := by
  funext i
  exact homogeneous_eval_smul (f.homogeneous i) a v

/-- Descent to actual projective points, proving representative independence. -/
def HomogeneousEndomorphism.onPoints {n : ℕ} (f : HomogeneousEndomorphism n) :
    ProjectivePoint n → ProjectivePoint n :=
  Projectivization.lift
    (fun v => Projectivization.mk ℂ (f.evalVector v) (f.noBasePoint v v.property))
    (by
      intro v w a h
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨a ^ f.degree, ?_⟩
      rw [← f.evalVector_smul, ← h])

@[simp] theorem HomogeneousEndomorphism.onPoints_mk {n : ℕ}
    (f : HomogeneousEndomorphism n) (v : CoordinateVector n) (hv : v ≠ 0) :
    f.onPoints (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (f.evalVector v) (f.noBasePoint v hv) := rfl

/-- Polynomial composition multiplies homogeneous degrees; no fiber-degree
identity is assumed in this construction. -/
def HomogeneousEndomorphism.comp {n : ℕ}
    (f g : HomogeneousEndomorphism n) : HomogeneousEndomorphism n where
  degree := g.degree * f.degree
  forms := fun i => MvPolynomial.eval₂ MvPolynomial.C g.forms (f.forms i)
  homogeneous := fun i => (f.homogeneous i).eval₂ _ _
    (fun c => MvPolynomial.isHomogeneous_C _ c) g.homogeneous
  noBasePoint := by
    intro v hv
    have h : (fun i => MvPolynomial.eval v
        (MvPolynomial.eval₂ MvPolynomial.C g.forms (f.forms i))) =
        f.evalVector (g.evalVector v) := by
      funext i
      exact (MvPolynomial.eval_assoc g.forms v (f.forms i)).symm
    rw [h]
    exact f.noBasePoint _ (g.noBasePoint v hv)

theorem HomogeneousEndomorphism.comp_evalVector {n : ℕ}
    (f g : HomogeneousEndomorphism n) (v : CoordinateVector n) :
    (f.comp g).evalVector v = f.evalVector (g.evalVector v) := by
  funext i
  exact (MvPolynomial.eval_assoc g.forms v (f.forms i)).symm

theorem HomogeneousEndomorphism.comp_onPoints {n : ℕ}
    (f g : HomogeneousEndomorphism n) :
    (f.comp g).onPoints = f.onPoints ∘ g.onPoints := by
  funext x
  induction x using Projectivization.ind with
  | h v hv =>
    simp only [Function.comp_apply, onPoints_mk, comp_evalVector]
    exact (f.onPoints_mk (g.evalVector v) (g.noBasePoint v hv)).symm

def HomogeneousEndomorphism.identity (n : ℕ) : HomogeneousEndomorphism n where
  degree := 1
  forms := MvPolynomial.X
  homogeneous := MvPolynomial.isHomogeneous_X ℂ
  noBasePoint := by intro v hv; simpa using hv

def HomogeneousEndomorphism.iterate {n : ℕ} (f : HomogeneousEndomorphism n) :
    ℕ → HomogeneousEndomorphism n
  | 0 => .identity n
  | k + 1 => f.comp (f.iterate k)

theorem HomogeneousEndomorphism.iterate_degree {n : ℕ}
    (f : HomogeneousEndomorphism n) (k : ℕ) :
    (f.iterate k).degree = f.degree ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => change (f.iterate k).degree * f.degree = _; rw [ih, pow_succ]

theorem HomogeneousEndomorphism.identity_onPoints (n : ℕ) :
    (HomogeneousEndomorphism.identity n).onPoints = id := by
  funext x
  induction x using Projectivization.ind with
  | h v hv =>
    rw [onPoints_mk]
    congr 1
    funext i
    exact MvPolynomial.eval_X i

theorem HomogeneousEndomorphism.iterate_onPoints {n : ℕ}
    (f : HomogeneousEndomorphism n) (k : ℕ) :
    (f.iterate k).onPoints = f.onPoints^[k] := by
  induction k with
  | zero => exact identity_onPoints n
  | succ k ih =>
    change (f.comp (f.iterate k)).onPoints = _
    rw [comp_onPoints, ih, Function.iterate_succ']

theorem HomogeneousEndomorphism.iterate_total_invariance {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : Set (ProjectivePoint n))
    (hV : f.onPoints ⁻¹' V = V) (k : ℕ) :
    (f.iterate k).onPoints ⁻¹' V = V := by
  rw [iterate_onPoints]
  exact total_invariance_iterate f.onPoints V hV k

/-- A homogeneous prime ideal giving a nonempty projective zero set.
No assertion about degree, smoothness, fibers or duality is packed into it. -/
structure IntegralProjectiveEquations (n : ℕ) where
  ideal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)
  prime : ideal.toIdeal.IsPrime
  nonempty : ∃ v : CoordinateVector n, v ≠ 0 ∧
    ∀ P ∈ ideal.toIdeal, MvPolynomial.eval v P = 0

theorem homogeneous_ideal_vanish_smul {n : ℕ}
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ))
    (v : CoordinateVector n) (hv : ∀ P ∈ I.toIdeal, MvPolynomial.eval v P = 0)
    (a : ℂ) : ∀ P ∈ I.toIdeal, MvPolynomial.eval (a • v) P = 0 := by
  intro P hP
  rw [← MvPolynomial.sum_homogeneousComponent P, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [homogeneous_eval_smul (MvPolynomial.homogeneousComponent_mem j P)]
  rw [hv _ (MvPolynomial.homogeneousComponent_mem_of_mem I.isHomogeneous hP j), mul_zero]

theorem homogeneous_ideal_vanish_unit_smul_iff {n : ℕ}
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ))
    (v : CoordinateVector n) (a : ℂˣ) :
    (∀ P ∈ I.toIdeal, MvPolynomial.eval (a • v) P = 0) ↔
      ∀ P ∈ I.toIdeal, MvPolynomial.eval v P = 0 := by
  constructor
  · intro h
    have hh := homogeneous_ideal_vanish_smul I (a • v) h (↑a⁻¹ : ℂ)
    simpa [Units.smul_def, smul_smul] using hh
  · intro h
    exact homogeneous_ideal_vanish_smul I v h a

def IntegralProjectiveEquations.zeroSet {n : ℕ} (V : IntegralProjectiveEquations n) :
    Set (ProjectivePoint n) :=
  {x | ∀ P ∈ V.ideal.toIdeal, MvPolynomial.eval x.rep P = 0}

theorem IntegralProjectiveEquations.mem_zeroSet_mk {n : ℕ}
    (V : IntegralProjectiveEquations n) (v : CoordinateVector n) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ V.zeroSet ↔
      ∀ P ∈ V.ideal.toIdeal, MvPolynomial.eval v P = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (∀ P ∈ V.ideal.toIdeal,
    MvPolynomial.eval (Projectivization.mk ℂ v hv).rep P = 0) ↔ _
  rw [← ha]
  exact homogeneous_ideal_vanish_unit_smul_iff V.ideal v a

theorem IntegralProjectiveEquations.zeroSet_nonempty {n : ℕ}
    (V : IntegralProjectiveEquations n) : V.zeroSet.Nonempty := by
  obtain ⟨v, hv, hV⟩ := V.nonempty
  exact ⟨Projectivization.mk ℂ v hv, (V.mem_zeroSet_mk v hv).mpr hV⟩

/-- Precise complex-point target. This declaration does NOT prove it.
The conclusion is equality to a genuine mathlib projective linear subspace.
The original Scheme theorem and the characteristic-zero extension remain
separate, unverified targets until the algebraic/geometric bridges are proved. -/
def LinearityTheoremGoal : Prop :=
  ∀ (n : ℕ) (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n),
    1 < f.degree → Function.Surjective f.onPoints →
    f.onPoints ⁻¹' V.zeroSet = V.zeroSet →
    ∃ W : Projectivization.Subspace ℂ (CoordinateVector n),
      (W : Set (ProjectivePoint n)) = V.zeroSet

end LinearStudy
