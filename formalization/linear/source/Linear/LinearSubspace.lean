module

public import Linear.Projective

/-! # Linear equations define genuine projective linear subspaces
This does not prove that a degree-one integral variety has such equations.
That Scheme/degree bridge remains separate.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

def linearEquationSubmodule {n : ℕ} {ι : Type*}
    (equations : ι → CoordinateVector n →ₗ[ℂ] ℂ) :
    Submodule ℂ (CoordinateVector n) := ⨅ i, LinearMap.ker (equations i)

def linearEquationSubspace {n : ℕ} {ι : Type*}
    (equations : ι → CoordinateVector n →ₗ[ℂ] ℂ) :
    Projectivization.Subspace ℂ (CoordinateVector n) :=
  (linearEquationSubmodule equations).projectivization

theorem mem_linearEquationSubmodule {n : ℕ} {ι : Type*}
    (equations : ι → CoordinateVector n →ₗ[ℂ] ℂ) (v : CoordinateVector n) :
    v ∈ linearEquationSubmodule equations ↔ ∀ i, equations i v = 0 := by
  simp [linearEquationSubmodule]

theorem mem_linearEquationSubspace {n : ℕ} {ι : Type*}
    (equations : ι → CoordinateVector n →ₗ[ℂ] ℂ)
    (v : CoordinateVector n) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ linearEquationSubspace equations ↔
      ∀ i, equations i v = 0 := by
  rw [linearEquationSubspace, Submodule.mk_mem_projectivization_iff]
  exact mem_linearEquationSubmodule equations v

end LinearStudy
