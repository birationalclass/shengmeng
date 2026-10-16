module
public import Linear.GradedModuleHomogeneousGenerators
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A M : Type*} [Field K] [CommRing A] [IsDomain A]
variable [AddCommGroup M] [Module K M] [Module A M] [Module.Finite A M]

/-- The ACTUAL generic module has a basis consisting of localized images of
homogeneous elements of the original module. Neither a homogeneous basis nor
its cardinality is supplied as an additional input. -/
theorem finiteModule_exists_generic_homogeneous_basis
    (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    {N : Type*} [AddCommGroup N] [Module A N] [Module F N] [IsScalarTower A F N]
    (l : M →ₗ[A] N) [IsLocalizedModule (nonZeroDivisors A) l] :
    ∃ (m : ℕ) (b : Fin m → M), m = Module.finrank F N ∧
      (∀ i, ∃ d : ℕ, b i ∈ ℳ d) ∧
      LinearIndependent F (fun i => l (b i)) ∧
      Submodule.span F (Set.range (fun i => l (b i))) = ⊤ := by
  classical
  obtain ⟨s, hs, hhom⟩ := finiteModule_exists_homogeneous_generators (A := A) ℳ
  let S : Set N := l '' (s : Set M)
  have hS : S.Finite := s.finite_toSet.image l
  have hspan : Submodule.span F S = ⊤ :=
    span_eq_top_of_isLocalizedModule F (nonZeroDivisors A) l hs
  letI : Module.Finite F (Submodule.span F S) := Module.Finite.span_of_finite F hS
  obtain ⟨u, hu, huspan, huli⟩ := Submodule.exists_fun_fin_finrank_span_eq F S
  have hex : ∀ i, ∃ x : M, x ∈ s ∧ l x = u i := fun i => hu i
  choose b hb using hex
  have hub : (fun i => l (b i)) = u := funext fun i => (hb i).2
  refine ⟨Module.finrank F (Submodule.span F S), b, ?_, ?_, ?_, ?_⟩
  · rw [hspan, finrank_top]
  · intro i
    exact hhom (b i) (hb i).1
  · rw [hub]
    exact huli
  · rw [hub, huspan, hspan]

end LinearStudy
