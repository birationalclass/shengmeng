module
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeProjectiveFiniteGradedFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ)+d))

/-- EVERY actual integer-degree native local-fraction sheaf is finitely
presented over a Noetherian actual graded ring, when its degree-one opens
cover Proj and its original module is finite. The shifted decomposition
and actual O_Proj-linear comparison are constructed, not assumed.
This proves positive-twist finiteness needed next; it does not prove Serre
vanishing or identify this model with the tensor-power line bundle. -/
theorem nativeFiniteGradedTwist_isFinitePresentation_of_cover
    [IsNoetherianRing S] [Module.Finite S M] (k : ℤ) {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k).IsFinitePresentation := by
  let 𝒟k := integerGradingShift 𝒟 k
  let hDk := integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k
  letI : DirectSum.Decomposition 𝒟k := integerGradingShiftDecomposition 𝒟 k
  letI : (nativeProjectiveModuleSheaf 𝓑 𝒟k hDk 0).IsFinitePresentation :=
    nativeFiniteGraded_isFinitePresentation_of_cover 𝓑 𝒟k hDk a ha hcover
  exact (SheafOfModules.isFinitePresentation (AlgebraicGeometry.Proj 𝓑).ringCatSheaf).prop_of_iso
    (nativeProjectiveTwistRegradingIso 𝓑 𝒟 hD k) inferInstance
end LinearStudy
