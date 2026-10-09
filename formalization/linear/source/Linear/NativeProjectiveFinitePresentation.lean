module
public import Linear.IntegerGradedFinitePresentation
public import Linear.NativeProjectivePrimeMapExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry Classical
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
include hD

/-- Construct a finite homogeneous presentation and prove exactness of
its ACTUAL maps at every original projective prime. This asserts ambient
prime-localization exactness, not yet exactness of the associated sheaves. -/
theorem nativeProjectiveFiniteGraded_exists_primeExact_presentation
    [IsNoetherianRing S] [Module.Finite S M] :
    ∃ s : Finset M,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
        Function.Surjective e ∧
          (∀ d : ℤ, ∀ f : s → S, f ∈ integerShiftedFreePiece 𝓑 w d → e f ∈ 𝒟 d) ∧
          ∃ t : Finset e.ker,
            letI := Classical.decEq t
            ∃ z : t → ℤ,
              let a := integerShiftedFreeGeneratorMap (S := S)
                (fun i : t => ((i : e.ker) : s → S))
              (∀ d : ℤ, ∀ f : t → S, f ∈ integerShiftedFreePiece 𝓑 z d →
                a f ∈ integerShiftedFreePiece 𝓑 w d) ∧
              ∀ p : ProjectiveSpectrum 𝓑,
                Function.Exact (nativeProjectiveModuleAtPrimeMap 𝓑 a p)
                  (nativeProjectiveModuleAtPrimeMap 𝓑 e p) := by
  obtain ⟨s, w, he, hh, t, z, hex, ha⟩ :=
    integerGradedFinite_exists_shiftedFree_presentation 𝓑 𝒟 hD
  refine ⟨s, w, he, hh, t, z, ha, ?_⟩
  intro p
  apply nativeProjectiveModuleAtPrimeMap_exact
  exact LinearMap.exact_iff.mpr hex.symm

end LinearStudy
