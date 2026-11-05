module
public import Linear.IntegerGradedFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open Classical
universe u
attribute [local instance] Classical.decEq
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
/-- Verified PRESENTATION DATA for an actual integer-graded finite module.
Choosing this data retains the specific original generator/relation maps,
all integer degrees,surjectivity,homogeneity and exactness. It does not
choose an arbitrary whole duality isomorphism or assert trace calibration. -/
structure IntegerGradedFinitePresentationData where
  generators : Finset M
  generatorDegrees : generators → ℤ
  generator_surjective : Function.Surjective
    (integerShiftedFreeGeneratorMap (S:=S) (fun i : generators => (i : M)))
  generator_homogeneous : ∀ d : ℤ,∀ f : generators → S,
    f ∈ integerShiftedFreePiece B generatorDegrees d →
      integerShiftedFreeGeneratorMap (S:=S) (fun i : generators => (i : M)) f ∈ D d
  relations : Finset (integerShiftedFreeGeneratorMap (S:=S) (fun i : generators => (i : M))).ker
  relationDegrees : relations → ℤ
  relation_exact : LinearMap.range
    (integerShiftedFreeGeneratorMap (S:=S)
      (fun i : relations => ((i : (integerShiftedFreeGeneratorMap (S:=S)
        (fun j : generators => (j : M))).ker) : generators → S))) =
      (integerShiftedFreeGeneratorMap (S:=S) (fun i : generators => (i : M))).ker
  relation_homogeneous : ∀ d : ℤ,∀ f : relations → S,
    f ∈ integerShiftedFreePiece B relationDegrees d →
      integerShiftedFreeGeneratorMap (S:=S)
        (fun i : relations => ((i : (integerShiftedFreeGeneratorMap (S:=S)
          (fun j : generators => (j : M))).ker) : generators → S)) f ∈
            integerShiftedFreePiece B generatorDegrees d
/-- Existing actual finite-presentation theorem supplies ALL fields of
presentation data. Desired comparison/naturality/duality is not an input. -/
theorem integerGradedFinitePresentationData_nonempty
    [IsNoetherianRing S] [Module.Finite S M]
    (hD : ∀ n : ℕ,∀ d : ℤ,∀ b : S,b ∈ B n →∀ x : M,x ∈ D d → b • x ∈ D ((n:ℤ)+d)) :
    Nonempty (IntegerGradedFinitePresentationData B D) := by
  classical
  obtain ⟨s,w,he,hh,t,z,hex,hhom⟩ := integerGradedFinite_exists_shiftedFree_presentation B D hD
  exact ⟨⟨s,w,he,hh,t,z,hex,hhom⟩⟩
/-- Choose verified PRESENTATION DATA,then future comparisons can be
constructed from its actual maps and related by the existing all-integer
presentation-map duality. No arbitrary whole-Iso choice occurs here. -/
def integerGradedFiniteChosenPresentationData
    [IsNoetherianRing S] [Module.Finite S M]
    (hD : ∀ n : ℕ,∀ d : ℤ,∀ b : S,b ∈ B n →∀ x : M,x ∈ D d → b • x ∈ D ((n:ℤ)+d)) :
    IntegerGradedFinitePresentationData B D :=
  Classical.choice (integerGradedFinitePresentationData_nonempty B D hD)
end LinearStudy
