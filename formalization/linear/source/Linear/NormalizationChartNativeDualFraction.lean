module
public import Linear.NormalizationChartFunctionalDenominator
public import Linear.NativeDualFullSourceChartComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  normalizationHomogeneousSourceChartAlgebra

/-- The integral homogeneous lift is in the ACTUAL native coextension
degree-m piece and keeps the original chart-functional evaluation. -/
theorem normalizationChartFunctional_exists_native_dual_fraction
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) :
    ∃ m : ℕ, ∃ ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R),
      ell ∈ coextensionGradedPiece 𝒜 𝓑 (m : ℤ) ∧
      ∀ n : ℕ, ∀ b : S, ∀ hb : b ∈ 𝓑 n,
        algebraMap R (Localization.Away a) (ell b) =
          (algebraMap R (Localization.Away a) a)^(n+m) *
            (f (HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb))).val := by
  obtain ⟨m,ψ,hψ⟩ := normalizationChartFunctional_exists_homogeneous_denominator
    𝒜 𝓑 a ha haB hinj f
  let ell := (coextensionGradedBaseEquiv (K := K) (R := R) (S := S)).symm ψ
  have hell (b : S) : ell b = ψ b := by
    have h := congrArg (fun g : S →ₗ[R] R => g b)
      ((coextensionGradedBaseEquiv (K := K) (R := R) (S := S)).apply_symm_apply ψ)
    exact h
  refine ⟨m,ell,?_,?_⟩
  · rw [coextensionGradedPiece_mem_iff]
    intro n b hb
    rw [hell]
    rw [← Int.natCast_add]
    simp only [gradedIntegerProjection,Int.natCast_nonneg,ite_true,Int.toNat_natCast]
    rw [gradedModuleProjection_on_piece 𝒜 (n+m) (n+m) (ψ b) (hψ n b hb).1]
    simp
  · intro n b hb
    rw [hell]
    exact (hψ n b hb).2
end LinearStudy
