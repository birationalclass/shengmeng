module
public import Linear.RectangularMinor
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace LinearStudy

/-- A split conormal map remains injective in coordinates after residue-field
base change. This constructs the rank hypothesis, rather than assuming it. -/
theorem split_basis_residue_coordinates_linearIndependent
    {R K C M ι σ : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M] [Finite σ]
    (b : Module.Basis ι R C) (c : Module.Basis σ R M)
    (f : C →ₗ[R] M) (l : M →ₗ[R] C) (hl : l.comp f = LinearMap.id) :
    LinearIndependent K (fun i j => algebraMap R K (c.repr (f (b i)) j)) := by
  have hh : (l.baseChange K).comp (f.baseChange K) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
  have hi : Function.Injective (f.baseChange K) := by
    apply Function.LeftInverse.injective (g := l.baseChange K)
    intro x
    exact DFunLike.congr_fun hh x
  have h := ((b.baseChange K).linearIndependent.map' (f.baseChange K)
    (LinearMap.ker_eq_bot.mpr hi)).map' (c.baseChange K).equivFun.toLinearMap
      (LinearMap.ker_eq_bot.mpr (c.baseChange K).equivFun.injective)
  convert h using 1
  funext i j
  simp only [Function.comp_apply, Module.Basis.baseChange_apply,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe, Module.Basis.equivFun_apply,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

theorem split_basis_residue_coordinates_nonzero_minor
    {R K C M σ : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M] [Finite σ] {n : ℕ}
    (b : Module.Basis (Fin n) R C) (c : Module.Basis σ R M)
    (f : C →ₗ[R] M) (l : M →ₗ[R] C) (hl : l.comp f = LinearMap.id) :
    ∃ j : Fin n → σ, Function.Injective j ∧
      Matrix.det (fun i k => algebraMap R K (c.repr (f (b i)) (j k))) ≠ 0 :=
  exists_nonzero_coordinate_minor _
    (split_basis_residue_coordinates_linearIndependent b c f l hl)

end LinearStudy
