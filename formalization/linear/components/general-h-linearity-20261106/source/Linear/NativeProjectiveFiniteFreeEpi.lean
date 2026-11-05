module
public import Linear.IntegerGradedFiniteFreeSurjection
public import Linear.NativeProjectiveHomogeneousSurjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Classical
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
include hD

/-- A finite actual integer-graded module receives a genuine native
Proj sheaf epimorphism from the actual associated sheaf of a constructed
shifted finite free module. No free presentation or sheaf epi is assumed. -/
theorem nativeProjectiveFiniteGraded_exists_shiftedFree_sheafEpi [Module.Finite S M] :
    ∃ s : Finset M,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let ℱ := integerShiftedFreePiece 𝓑 w
        let hF := integerShiftedFreePiece_smul_homogeneous 𝓑 w
        let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
        ∃ hh : ∀ d : ℤ, ∀ f : s → S, f ∈ ℱ d → e f ∈ 𝒟 (d + 0),
          Function.Surjective e ∧
            Epi (nativeProjectiveModuleSheafMap 𝓑 ℱ 𝒟 hF hD 0 e hh 0) := by
  classical
  obtain ⟨s, w, he, hh⟩ := integerGradedFinite_exists_shiftedFree_surjection 𝓑 𝒟 hD
  letI := integerShiftedFreeDecomposition 𝓑 w
  let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
  have hh0 : ∀ d : ℤ, ∀ f : s → S, f ∈ integerShiftedFreePiece 𝓑 w d →
      e f ∈ 𝒟 (d + 0) := by simpa only [add_zero] using hh
  exact ⟨s, w, hh0, he, nativeProjectiveHomogeneousSurjectionSheaf_epi 𝓑
    (integerShiftedFreePiece 𝓑 w) 𝒟
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD e hh0 he 0⟩

end LinearStudy
