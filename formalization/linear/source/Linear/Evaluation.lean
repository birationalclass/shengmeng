module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic
public import Linear.Projective

/-! # The finite-point linear algebra of the lifting argument
These checked results concern actual linear maps and their kernels. The Koszul
exact sequence and proper-duality identification must still be constructed
geometrically. No such sequence is postulated as a new axiom.
-/

@[expose] public section
noncomputable section
namespace LinearStudy
variable {K ι U M : Type*} [Field K] [Fintype ι] [DecidableEq ι]
  [AddCommGroup U] [Module K U] [AddCommGroup M] [Module K M]

def weightedEvaluation (lam : ι → K) : (ι → K) →ₗ[K] K :=
  ∑ i, lam i • LinearMap.proj i

omit [DecidableEq ι] in
theorem weightedEvaluation_apply (lam v : ι → K) :
    weightedEvaluation lam v = ∑ i, lam i * v i := by
  simp [weightedEvaluation, LinearMap.sum_apply]

@[simp] theorem weightedEvaluation_single (lam : ι → K) (i : ι) :
    weightedEvaluation lam (Pi.single i 1) = lam i := by
  simp [weightedEvaluation_apply, Pi.single_apply]

theorem weightedEvaluation_nonzero (lam : ι → K) (hlam : lam ≠ 0) :
    weightedEvaluation lam ≠ 0 := by
  intro hz
  apply hlam
  funext i
  have h := weightedEvaluation_single lam i
  rw [hz, LinearMap.zero_apply] at h
  exact h.symm

omit [DecidableEq ι] in
/-- Extend a relation by zero from the first fiber to the whole point set. -/
theorem extend_relation_by_zero (lam : ι → K) (S₁ : Finset ι)
    (hlam : ∀ i ∉ S₁, lam i = 0) (v : ι → K) :
    weightedEvaluation lam v = ∑ i ∈ S₁, lam i * v i := by
  rw [weightedEvaluation_apply]
  symm
  apply Finset.sum_subset (Finset.subset_univ S₁)
  intro i _ hi
  rw [hlam i hi, zero_mul]

/-- Exactness lets a relation factor through the connecting map. -/
theorem relation_factors_through_exact_sequence
    (E : U →ₗ[K] (ι → K)) (D : (ι → K) →ₗ[K] M)
    (hD : Function.Surjective D) (hexact : LinearMap.ker D = LinearMap.range E)
    (lam : ι → K) (hrelation : ∀ u, weightedEvaluation lam (E u) = 0) :
    ∃ a : M →ₗ[K] K, a.comp D = weightedEvaluation lam := by
  have hker : LinearMap.ker D ≤ LinearMap.ker (weightedEvaluation lam) := by
    rw [hexact]
    rintro v ⟨u, rfl⟩
    exact hrelation u
  refine ⟨D.liftOfSurjective hD ⟨weightedEvaluation lam, hker⟩, ?_⟩
  ext v
  exact D.equivOfSurjective_apply hD hker

/-- A nonzero relation produces a nonzero lifted functional. -/
theorem factored_relation_nonzero (lam : ι → K) (hlam : lam ≠ 0)
    (D : (ι → K) →ₗ[K] M) (a : M →ₗ[K] K)
    (ha : a.comp D = weightedEvaluation lam) : a ≠ 0 := by
  intro hz
  apply weightedEvaluation_nonzero lam hlam
  rw [← ha, hz, LinearMap.zero_comp]

/-- In an explicit pointwise duality identification, zero is equivalent to
zero weight. This is algebraic transport; it does not construct the geometric
identification for canonical-sheaf fibers. -/
theorem duality_zero_iff (W : Type*) [AddCommGroup W] [Module K W]
    (β : W ≃ₗ[K] K) (a : W) (lam : K) (h : β a = lam) :
    a = 0 ↔ lam = 0 := by
  rw [← h]
  exact β.map_eq_zero_iff.symm

/-- The actual restriction of degree-t homogeneous forms to chosen point
representatives; this is not assumed to be surjective. -/
def homogeneousPointEvaluation {n : ℕ} (t : ℕ)
    (points : ι → CoordinateVector n) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ t →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi (fun i => (MvPolynomial.aeval (points i)).toLinearMap.comp
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ t).subtype)

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneousPointEvaluation_apply {n : ℕ} (t : ℕ)
    (points : ι → CoordinateVector n)
    (P : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ t) (i : ι) :
    homogeneousPointEvaluation t points P i = MvPolynomial.eval (points i) P := by
  simp [homogeneousPointEvaluation]

omit [DecidableEq ι] in
/-- Rescaling point representatives requires inverse degree-t rescaling of
the weights. Nonzero scalars are explicit units, so no denominator is omitted. -/
theorem rescaled_evaluation_relation {σ : Type*}
    {P : MvPolynomial σ K} {t : ℕ} (hP : P.IsHomogeneous t)
    (points : ι → σ → K) (scalars : ι → Kˣ) (weights : ι → K) :
    (∑ i, (weights i / (scalars i : K) ^ t) *
      MvPolynomial.eval ((scalars i : K) • points i) P) =
    ∑ i, weights i * MvPolynomial.eval (points i) P := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [homogeneous_eval_smul hP]
  have hne : (scalars i : K) ^ t ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  field_simp

omit [DecidableEq ι] in
theorem rescaled_evaluation_relation_zero {σ : Type*}
    {P : MvPolynomial σ K} {t : ℕ} (hP : P.IsHomogeneous t)
    (points : ι → σ → K) (scalars : ι → Kˣ) (weights : ι → K)
    (h : (∑ i, weights i * MvPolynomial.eval (points i) P) = 0) :
    (∑ i, (weights i / (scalars i : K) ^ t) *
      MvPolynomial.eval ((scalars i : K) • points i) P) = 0 := by
  rw [rescaled_evaluation_relation hP points scalars weights, h]

end LinearStudy
