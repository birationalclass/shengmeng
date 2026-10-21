module
public import Linear.NativeProjectiveShiftedFreeChart
public import Linear.SheafFreePresentationOfExact
public import Linear.NativeProjectiveExactFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
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

/-- The actual finite graded module sheaf has a constructed actual
free sheaf presentation on every original degree-one chart. -/
theorem nativeFiniteGradedChartPresentation_nonempty
    (v : S) (hv : v ∈ 𝓑 1) (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, v ∉ p.1.asHomogeneousIdeal) :
    Nonempty ((nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).over U).Presentation := by
  classical
  obtain ⟨s, w, hh, he, hepi, t, z, ha, hex, hc⟩ :=
    nativeProjectiveFiniteGraded_exists_exact_native_presentation 𝓑 𝒟 hD
  let ℰ := integerShiftedFreePiece 𝓑 w
  let hE := integerShiftedFreePiece_smul_homogeneous 𝓑 w
  let ℛ := integerShiftedFreePiece 𝓑 z
  let hR := integerShiftedFreePiece_smul_homogeneous 𝓑 z
  let : DirectSum.Decomposition ℰ := integerShiftedFreeDecomposition 𝓑 w
  let : DirectSum.Decomposition ℛ := integerShiftedFreeDecomposition 𝓑 z
  let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
  let a := integerShiftedFreeGeneratorMap (S := S)
    (fun i : t => ((i : e.ker) : s → S))
  let c := ShortComplex.mk
    (nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ ℰ hR hE a ha 0)
    (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD e hh 0)
    (nativeProjectiveDegreeZeroSheafMap_comp_zero 𝓑 ℛ ℰ 𝒟
      hR hE hD a e ha hh hex 0)
  have hc' : c.Exact := hc
  let : Epi c.g := hepi
  let F := SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝓑).ringCatSheaf U
  let : F.Additive := nativeSheafOverFunctor_additive 𝓑 U
  let : F.IsLeftAdjoint := nativeSheafOverFunctor_isLeftAdjoint 𝓑 U
  let cU := c.map F
  have hcU : IsColimit (CokernelCofork.ofπ cU.g cU.zero) :=
    CokernelCofork.mapIsColimit _ hc'.gIsCokernel F
  have hexU : cU.Exact := cU.exact_of_g_is_cokernel hcU
  let : Epi cU.g := epi_of_isColimit_cofork hcU
  exact ⟨sheafFreePresentationOfExact cU hexU
    (nativeShiftedFreeChartIso 𝓑 z v hv U hp)
    (nativeShiftedFreeChartIso 𝓑 w v hv U hp)⟩

/-- Choose one of the actual local presentations whose existence
has been proved from the actual finite graded module. -/
def nativeFiniteGradedChartPresentation
    (v : S) (hv : v ∈ 𝓑 1) (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, v ∉ p.1.asHomogeneousIdeal) :
    ((nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).over U).Presentation :=
  Classical.choice (nativeFiniteGradedChartPresentation_nonempty 𝓑 𝒟 hD v hv U hp)

end LinearStudy
