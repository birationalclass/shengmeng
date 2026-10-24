module
public import Linear.GradedGenericHomogeneousBasis
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R M N : Type*} [CommRing R] [IsDomain R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N]

/-- A submodule that spans the ACTUAL generic fiber contains a single
nonzero scalar multiple of the whole finite module. This clears all
denominators simultaneously, without assuming a common denominator. -/
theorem finiteModule_genericSpan_exists_common_denominator
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    [Module F N] [IsScalarTower R F N]
    (l : M →ₗ[R] N) [IsLocalizedModule (nonZeroDivisors R) l]
    (P : Submodule R M)
    (hP : P.localized' F (nonZeroDivisors R) l = ⊤) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : M, r • x ∈ P := by
  let g := P.toLocalizedQuotient' F (nonZeroDivisors R) l
  have hzero : ∀ x : M ⧸ P, g x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := P.mkQ_surjective x
    change (Submodule.Quotient.mk (l y) : N ⧸ P.localized' F (nonZeroDivisors R) l) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [hP]
    trivial
  have ht : Module.IsTorsion R (M ⧸ P) := by
    intro x
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
      (S := nonZeroDivisors R) (f := g) ((hzero x).trans (hzero 0).symm)
    exact ⟨s, by simpa using hs⟩
  obtain ⟨r, hr⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  refine ⟨r, nonZeroDivisors.ne_zero hr.2, ?_⟩
  apply (Module.isTorsionBy_quotient_iff P r).mp
  intro x
  exact Submodule.mem_annihilator.mp hr.1 x (Submodule.mem_top)

/-- The same common-denominator conclusion for an actual family whose
localized images span the generic module. -/
theorem finiteModule_genericFamily_exists_common_denominator
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    [Module F N] [IsScalarTower R F N]
    (l : M →ₗ[R] N) [IsLocalizedModule (nonZeroDivisors R) l]
    {ι : Type*} (b : ι → M)
    (hb : Submodule.span F (Set.range (fun i => l (b i))) = ⊤) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : M, r • x ∈ Submodule.span R (Set.range b) := by
  apply finiteModule_genericSpan_exists_common_denominator F l
  rw [Submodule.localized'_span, ← Set.range_comp', hb]

end LinearStudy
