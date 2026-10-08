module
public import Linear.FreeAwayFiberRank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy

/-- A constructed nonempty principal open makes every field-valued fiber
of an actual finite module have its generic rank. Evaluation maps are
arbitrary ring homomorphisms and need not be injective. -/
theorem finiteModule_exists_fiber_rank_open
    {R M K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Field K] :
    ∃ r : R, r ≠ 0 ∧ ∀ ρ : R →+* K, ρ r ≠ 0 →
      (letI : Algebra R K := ρ.toAlgebra
       Module.finrank K (K ⊗[R] M) = Module.finrank R M) := by
  obtain ⟨r, hr, hfree, _⟩ := finiteModule_exists_free_away (R := R) (M := M)
  refine ⟨r, hr, ?_⟩
  intro ρ hρ
  letI : Algebra R K := ρ.toAlgebra
  letI := hfree
  exact module_tensor_finrank_eq_of_free_away r hr hρ

end LinearStudy
