module
public import Linear.IntegerShiftedFreeGeneratorMap
public import Linear.IntegerGradedModuleGenerators
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open Classical
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
include hD

/-- A finite actual integer-graded module receives a constructed
degree-preserving surjection from an actual shifted finite free module.
Neither its free module, generator degrees, nor surjection is supplied. -/
theorem integerGradedFinite_exists_shiftedFree_surjection [Module.Finite S M] :
    ∃ s : Finset M,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        Function.Surjective (integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))) ∧
          ∀ d : ℤ, ∀ f : s → S, f ∈ integerShiftedFreePiece 𝓑 w d →
            integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M)) f ∈ 𝒟 d := by
  classical
  obtain ⟨s, hs, hh⟩ := integerGradedModule_exists_homogeneous_generators (A := S) 𝒟
  let w : s → ℤ := fun i => Classical.choose (hh i i.property)
  have hw : ∀ i : s, (i : M) ∈ 𝒟 (w i) :=
    fun i => Classical.choose_spec (hh i i.property)
  have hrange : Set.range (fun i : s => (i : M)) = (s : Set M) := by
    ext x
    simp
  have hgen : Submodule.span S (Set.range (fun i : s => (i : M))) = ⊤ := by
    rw [hrange]
    exact hs
  exact ⟨s, w, integerShiftedFreeGeneratorMap_surjective _ hgen,
    integerShiftedFreeGeneratorMap_homogeneous 𝓑 𝒟 hD w _ hw⟩

end LinearStudy
