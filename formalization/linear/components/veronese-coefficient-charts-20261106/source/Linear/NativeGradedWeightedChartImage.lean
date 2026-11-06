module
public import Linear.NativeGradedWeightedSingleFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u
variable {K R T X Y : Type u} [Field K] [CommRing R] [CommRing T]
variable [Algebra K R] [Algebra K T] [AddCommGroup X] [AddCommGroup Y]
variable [Module K X] [Module K Y] [Module R X] [Module T Y]
variable (A : ℕ → Submodule K R) (A' : ℕ → Submodule K T)
variable [GradedAlgebra A] [GradedAlgebra A']
variable (D : ℤ → Submodule K X) (D' : ℤ → Submodule K Y)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- Compare the native weighted chart carriers by their single homogeneous
fractions, with exact numerator degrees and the same powers of the denominators. -/
theorem nativeGradedWeightedChart_image
    (hD : ∀ (n : ℕ) (j : ℤ) (c : R), c ∈ A n →
      ∀ x : X, x ∈ D j → c • x ∈ D ((n : ℤ) + j))
    (hD' : ∀ (n : ℕ) (j : ℤ) (c : T), c ∈ A' n →
      ∀ y : Y, y ∈ D' j → c • y ∈ D' ((n : ℤ) + j))
    (d e : ℕ) (a : R) (b : T) (ha : a ∈ A d) (hb : b ∈ A' e)
    (i : X → Y)
    (hi : ∀ n : ℕ, i '' (D ((n*d : ℕ) : ℤ) : Set X) = (D' ((n*e : ℕ) : ℤ) : Set Y))
    (φ : LocalizedModule (Submonoid.powers a) X → LocalizedModule (Submonoid.powers b) Y)
    (hφ : ∀ (n : ℕ) (x : X),
      φ (LocalizedModule.mk x (⟨a^n, ⟨n,rfl⟩⟩ : Submonoid.powers a)) =
        LocalizedModule.mk (i x) (⟨b^n, ⟨n,rfl⟩⟩ : Submonoid.powers b)) :
    φ '' (nativeGradedModuleAwayDegreeZero A D d a : Set _) =
      (nativeGradedModuleAwayDegreeZero A' D' e b : Set _) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨n, x, hx, rfl⟩ := nativeGradedModuleAwayDegreeZero_exists_fraction A D hD d a ha z hz
    rw [hφ]
    apply Submodule.subset_span
    refine ⟨n, i x, ?_, rfl⟩
    have him : i x ∈ i '' (D ((n*d : ℕ) : ℤ) : Set X) := ⟨x, hx, rfl⟩
    exact (congrArg (fun U : Set Y => i x ∈ U) (hi n)).mp him
  · intro z hz
    obtain ⟨n, y, hy, rfl⟩ := nativeGradedModuleAwayDegreeZero_exists_fraction A' D' hD' e b hb z hz
    have him : y ∈ i '' (D ((n*d : ℕ) : ℤ) : Set X) := (hi n).symm ▸ hy
    obtain ⟨x, hx, rfl⟩ := him
    refine ⟨LocalizedModule.mk x ⟨a^n,⟨n,rfl⟩⟩, ?_, hφ n x⟩
    exact Submodule.subset_span ⟨n, x, hx, rfl⟩

end LinearStudy
#check LinearStudy.nativeGradedWeightedChart_image
#print axioms LinearStudy.nativeGradedWeightedChart_image

