module
public import Linear.NativeProjectivePolynomialSections
public import Linear.NativeRingIntegerDecomposition
public import Linear.NativeFiniteGradedSectionsLift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open LinearStudy AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual section of an actual homogeneous quotient module on
the original projective space is, in ALL sufficiently large degrees,
the image of an ORIGINAL homogeneous polynomial of that EXACT degree.
The bound is constructed before all later degrees and sections, and
neither an H1 certificate nor a global polynomial-lifting input is used. -/
theorem coordinateNativeGradedQuotient_eventually_polynomial_lift
    {F : Type u} [AddCommGroup F] [Module K F] [Module (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F]
    (G : ℤ → Submodule K F) [DirectSum.Decomposition G]
    (hG : ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
      c ∈ homogeneousSubmodule σ K a → ∀ x : F, x ∈ G d → c • x ∈ G ((a : ℤ)+d))
    (b : MvPolynomial σ K →ₗ[MvPolynomial σ K] F)
    (hh : ∀ d : ℤ, ∀ x : MvPolynomial σ K,
      x ∈ nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K) d → b x ∈ G d)
    (hb : Function.Surjective b) (j : σ) :
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∀ s : Γ(nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) G hG (N : ℤ), ⊤),
        ∃ Q : homogeneousSubmodule σ K N,
          ((nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
            (nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)) G
            (nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K)) hG b hh
            (N : ℤ)).app ⊤)
            (nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) N Q) = s := by
  let D := nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
  let hD := nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K)
  letI : DirectSum.Decomposition D :=
    nativeProjectiveRingIntegerDecomposition (homogeneousSubmodule σ K)
  obtain ⟨n₀,hn₀⟩ := coordinateNativeFiniteGraded_eventually_sections_surjective
    D G hD hG b hh hb j
  refine ⟨n₀,fun N hN s => ?_⟩
  obtain ⟨t,ht⟩ := hn₀ N hN s
  obtain ⟨Q,hQ⟩ := coordinateNativePositiveTwist_polynomial_sections_surjective (K := K) j N t
  exact ⟨Q,by rw [hQ]; exact ht⟩
end MvPolynomial
