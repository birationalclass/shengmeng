module
public import Linear.NativeProjectiveFiniteGradedFiniteChart
public import Linear.NativeProjectiveDegreeOneCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ) + d))
variable [IsNoetherianRing S] [Module.Finite S M]

/-- Actual local free-source presentations on the actual native
degree-one cover give quasicoherent data for the original module sheaf. -/
def nativeFiniteGradedFiniteQuasicoherentData {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).QuasicoherentData where
  I := ι
  X i := Proj.basicOpen 𝓑 (a i)
  coversTop := (Opens.coversTop_iff _ _).mpr hcover
  presentation i := nativeFiniteGradedFiniteChartPresentation 𝓑 𝒟 hD
    (a i) (ha i) (Proj.basicOpen 𝓑 (a i)) (fun p => p.2)

/-- Each actual chart presentation has finite generator and relation types. -/
theorem nativeFiniteGradedFiniteQuasicoherentData_isFinitePresentation {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeFiniteGradedFiniteQuasicoherentData 𝓑 𝒟 hD a ha hcover).IsFinitePresentation := by
  constructor
  intro i
  exact nativeFiniteGradedFiniteChartPresentation_isFinite 𝓑 𝒟 hD
    (a i) (ha i) (Proj.basicOpen 𝓑 (a i)) (fun p => p.2)

/-- Finite presentation of the ACTUAL native associated sheaf follows
from its constructed finite free-source presentations on the actual cover. -/
theorem nativeFiniteGraded_isFinitePresentation_of_cover {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsFinitePresentation := by
  apply SheafOfModules.IsFinitePresentation.mk
  exact ⟨nativeFiniteGradedFiniteQuasicoherentData 𝓑 𝒟 hD a ha hcover,
    nativeFiniteGradedFiniteQuasicoherentData_isFinitePresentation 𝓑 𝒟 hD a ha hcover⟩

end LinearStudy
