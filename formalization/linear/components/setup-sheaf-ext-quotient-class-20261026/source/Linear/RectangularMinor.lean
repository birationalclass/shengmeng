module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- A row-independent rectangular matrix has a nonzero maximal minor,
selected from the original coordinate columns, without a supplied inverse. -/
theorem exists_nonzero_coordinate_minor {K σ : Type*} [Field K] {n : ℕ}
    (A : Fin n → σ → K) (hA : LinearIndependent K A) :
    ∃ j : Fin n → σ, Function.Injective j ∧
      Matrix.det (fun i k => A i (j k)) ≠ 0 := by
  classical
  have hs : Submodule.span K (Set.range (flip A)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hA
  let b := Module.Basis.ofSpan hs.ge
  let e := b.indexEquiv (Pi.basisFun K (Fin n))
  let b' := b.reindex e
  have hm : ∀ i : Fin n, b' i ∈ Set.range (flip A) := by
    intro i
    dsimp only [b']
    rw [Module.Basis.reindex_apply]
    exact Module.Basis.ofSpan_subset hs.ge ⟨e.symm i, rfl⟩
  choose j hj using hm
  refine ⟨j, ?_, ?_⟩
  · intro i k hik
    apply b'.injective
    rw [← hj i, ← hj k, hik]
  · apply Matrix.nonsingular_iff_det_ne_zero.mp
    apply Matrix.Nonsingular.of_linearIndependent_col
    change LinearIndependent K (fun k i => A i (j k))
    have he : (fun k i => A i (j k)) = b' := funext hj
    rw [he]
    exact b'.linearIndependent

end LinearStudy
