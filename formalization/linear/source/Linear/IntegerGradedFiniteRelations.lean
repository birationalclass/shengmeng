module
public import Linear.IntegerGradedFiniteFreeSurjection
public import Linear.IntegerGradedKernelGenerators
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open Classical
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
include hD

/-- Finite homogeneous generators and finite homogeneous relations
for an actual integer-graded module over a noetherian original ring.
The kernel and its homogeneous generators are actual constructions. -/
theorem integerGradedFinite_exists_shiftedFree_homogeneous_relations
    [IsNoetherianRing S] [Module.Finite S M] :
    ∃ s : Finset M,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
        Function.Surjective e ∧
          (∀ d : ℤ, ∀ f : s → S, f ∈ integerShiftedFreePiece 𝓑 w d → e f ∈ 𝒟 d) ∧
          ∃ t : Finset e.ker, Submodule.span S (t : Set e.ker) = ⊤ ∧
            ∀ x ∈ t, ∃ d : ℤ, (x : s → S) ∈ integerShiftedFreePiece 𝓑 w d := by
  classical
  obtain ⟨s, w, he, hh⟩ := integerGradedFinite_exists_shiftedFree_surjection 𝓑 𝒟 hD
  let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
  letI := integerShiftedFreeDecomposition 𝓑 w
  obtain ⟨t, ht, hthom⟩ := integerDegreeZeroMap_kernel_exists_homogeneous_generators
    (integerShiftedFreePiece 𝓑 w) 𝒟 e hh
  exact ⟨s, w, he, hh, t, ht, hthom⟩

end LinearStudy
