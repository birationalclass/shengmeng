module
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Algebraic power-series evaluation at finite nilpotent tuples

Choose discrete uniformities internally and use the inspected mathlib
evaluation construction. The resulting ring/algebra maps have the required
constant and variable values and commute with arbitrary ring homomorphisms.
This is a foundation for diagonal comparisons, not a Jacobian trace identity.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem powerSeries_hasEval_of_nilpotent [TopologicalSpace S]
    (a : Fin n → S) (ha : ∀ i, IsNilpotent (a i)) : MvPowerSeries.HasEval a := by
  constructor
  · exact fun i => (ha i).isTopologicallyNilpotent
  · rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

def nilpotentPowerSeriesEval (f : R →+* S) (a : Fin n → S)
    (ha : ∀ i, IsNilpotent (a i)) : MvPowerSeries (Fin n) R →+* S := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  exact MvPowerSeries.eval₂Hom (φ := f) (a := a) (continuous_of_discreteTopology)
    (powerSeries_hasEval_of_nilpotent a ha)

theorem nilpotentPowerSeriesEval_C (f : R →+* S) (a : Fin n → S)
    (ha : ∀ i, IsNilpotent (a i)) (b : R) :
    nilpotentPowerSeriesEval f a ha (MvPowerSeries.C b) = f b := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  unfold nilpotentPowerSeriesEval
  rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]

theorem nilpotentPowerSeriesEval_X (f : R →+* S) (a : Fin n → S)
    (ha : ∀ i, IsNilpotent (a i)) (i : Fin n) :
    nilpotentPowerSeriesEval f a ha (MvPowerSeries.X i) = a i := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  unfold nilpotentPowerSeriesEval
  rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]

theorem nilpotentPowerSeriesEval_comp {T : Type*} [CommRing T]
    (f : R →+* S) (g : S →+* T) (a : Fin n → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    g.comp (nilpotentPowerSeriesEval f a ha) =
      nilpotentPowerSeriesEval (g.comp f) (fun i => g (a i))
        (fun i => (ha i).map g) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  let : UniformSpace T := ⊥
  apply RingHom.ext
  intro h
  unfold nilpotentPowerSeriesEval
  simp only [RingHom.comp_apply, MvPowerSeries.coe_eval₂Hom]
  exact congrFun (MvPowerSeries.comp_eval₂ (φ := f)
    continuous_of_discreteTopology (powerSeries_hasEval_of_nilpotent a ha)
    (ε := g) continuous_of_discreteTopology) h

def nilpotentPowerSeriesAlgEval [Algebra R S] (a : Fin n → S)
    (ha : ∀ i, IsNilpotent (a i)) : MvPowerSeries (Fin n) R →ₐ[R] S :=
  { nilpotentPowerSeriesEval (algebraMap R S) a ha with
    commutes' := fun b => by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self]
      exact nilpotentPowerSeriesEval_C (algebraMap R S) a ha b }

end LinearStudy
