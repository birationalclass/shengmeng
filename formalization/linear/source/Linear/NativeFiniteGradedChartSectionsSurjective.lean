module
public import Linear.QuasicoherentAffineOpenSections
public import Linear.NativeShiftedFreeChartSectionsSurjective
public import Linear.NativeChartSectionsModuleNaturality
public import Linear.NativeProjectiveFiniteGradedQuasicoherent
public import Linear.NativeProjectiveFiniteFreeEpi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 d → b • m ∈ 𝒟 ((n : ℤ)+d))
variable [IsNoetherianRing S] [Module.Finite S M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule

/-- For the actual finite integer-graded module, every actual native
sheaf section on an original degree-one chart comes from its original
degree-zero localized module. Quasicoherence and the free-source epi
are constructed from finite homogeneous generators, not supplied. -/
theorem nativeFiniteGradedChartDegreeZeroSectionMap_surjective
    {ι : Type u} (coords : ι → S) (hcoords : ∀ i, coords i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range coords) = ⊤)
    (a : S) (ha : a ∈ 𝓑 1) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha) := by
  classical
  haveI : (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsQuasicoherent :=
    nativeFiniteGraded_isQuasicoherent 𝓑 𝒟 hD coords hcoords hgen
  obtain ⟨s,w,hh,he,hepi⟩ :=
    nativeProjectiveFiniteGraded_exists_shiftedFree_sheafEpi 𝓑 𝒟 hD
  let ℱ := integerShiftedFreePiece 𝓑 w
  let hF := integerShiftedFreePiece_smul_homogeneous 𝓑 w
  let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
  letI := integerShiftedFreeDecomposition 𝓑 w
  haveI : (nativeProjectiveModuleSheaf 𝓑 ℱ hF 0).IsQuasicoherent :=
    nativeFiniteGraded_isQuasicoherent 𝓑 ℱ hF coords hcoords hgen
  let φ := nativeProjectiveModuleSheafMap 𝓑 ℱ 𝒟 hF hD 0 e hh 0
  haveI : Epi φ := hepi
  haveI : (nativeProjectiveModuleSheaf 𝓑 𝒟 hD (0+0)).IsQuasicoherent := by
    simpa only [add_zero] using (inferInstance : (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsQuasicoherent)
  have hsurj := quasicoherent_sections_surjective_on_nativeProjChart 𝓑
    1 (by omega) a ha φ
  change Function.Surjective
    (nativeProjectiveModuleSectionMap 𝓑 ℱ 𝒟 hF hD 0 e hh 0
      (op (ProjectiveSpectrum.basicOpen 𝓑 a))) at hsurj
  intro f
  obtain ⟨g,hg⟩ := hsurj f
  obtain ⟨x,hx⟩ := nativeShiftedFreeChartDegreeZeroSectionMap_surjective 𝓑 w a ha g
  let y := LocalizedModule.map (Submonoid.powers a) e x.1
  have hy : y ∈ nativeGradedModuleAwayDegreeZero 𝓑 𝒟 1 a :=
    nativeGradedModuleAwayDegreeZero_moduleMap_mem 𝓑 ℱ 𝒟 e hh 1 a x.1 x.property
  refine ⟨⟨y,hy⟩,?_⟩
  apply Subtype.ext
  funext p
  have hxp := congrArg (fun z => z.1 p) hx
  change nativeProjectiveChartRefinement 𝓑 a x.1 p = g.1 p at hxp
  have hgp := congrArg (fun z => z.1 p) hg
  change nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (g.1 p) = f.1 p at hgp
  change nativeProjectiveChartRefinement 𝓑 a y p = f.1 p
  rw [nativeProjectiveChartRefinement_moduleMap]
  change nativeProjectiveModuleAtPrimeMap 𝓑 e p.1
    (nativeProjectiveChartRefinement 𝓑 a x.1 p) = f.1 p
  rw [hxp]
  exact hgp

end LinearStudy
