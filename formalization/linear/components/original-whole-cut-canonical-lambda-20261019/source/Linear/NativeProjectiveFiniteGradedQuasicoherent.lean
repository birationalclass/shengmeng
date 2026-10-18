module
public import Linear.NativeProjectiveFiniteGradedChartPresentation
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
def nativeFiniteGradedQuasicoherentData {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).QuasicoherentData where
  I := ι
  X i := Proj.basicOpen 𝓑 (a i)
  coversTop := (Opens.coversTop_iff _ _).mpr hcover
  presentation i := nativeFiniteGradedChartPresentation 𝓑 𝒟 hD
    (a i) (ha i) (Proj.basicOpen 𝓑 (a i)) (fun p => p.2)

/-- Quasicoherence is deduced for the actual native associated sheaf
from the actual finite graded module, without being assumed as data. -/
theorem nativeFiniteGraded_isQuasicoherent {ι : Type u}
    (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsQuasicoherent :=
  (nativeFiniteGradedQuasicoherentData 𝓑 𝒟 hD a ha
    (degreeOneGenerated_nativeProj_cover 𝓑 a ha hgen)).isQuasicoherent

end LinearStudy
