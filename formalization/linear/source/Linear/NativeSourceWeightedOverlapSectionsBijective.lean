module
public import Linear.NativeSourceOverlapSectionsComparison
public import Linear.NativeSourceSpecOverlapOldLinear
public import Linear.NativeSourceSpecOverlapRestriction
public import Linear.NativeGradedDegreeOneOverlapLocalization
public import Linear.NativeSourceSpecChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsNoetherianRing S] [Module.Finite S M] [IsDomain S] [Module.IsTorsionFree S M]
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeSourceSpecChartSectionsModule
/-- The OLD actual weighted chart-to-Proj-section map is bijective on the
original coordinate product. Only the actual single-chart bijection is used;
the overlap localization, scalar transport and map identity are all proved. -/
theorem nativeSourceWeightedOverlapSections_bijective
    {ι : Type u} (coords : ι → S) (hcoords : ∀ i, coords i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range coords) = ⊤)
    (a b : S) (ha : a ∈ 𝓑 1) (hb : b ∈ 𝓑 1) (hab : a*b ≠ 0)
    (hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha)) :
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 (a*b)
      (SetLike.mul_mem_graded ha hb)) := by
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let j := Proj.awayι 𝓑 a ha (by decide)
  let Q := F.restrict j
  let W := PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb)
  letI := nativeGradedDegreeOneOverlapBaseModule 𝓑 𝒟 a b hb
  letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Q,W) :=
    inferInstanceAs <| Module (HomogeneousLocalization.Away 𝓑 a)
      (((modulesSpecToSheaf (R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).obj Q).obj.obj (op W))
  let E := nativeSourceOverlapLocalizedSectionsLinearEquiv 𝓑 𝒟 hD coords hcoords hgen
    a b ha hb hab hs
  let T := nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 (a*b) (SetLike.mul_mem_graded ha hb)
  let EW := schemeModuleSpecOpenSectionsEquiv F j W (Proj.basicOpen 𝓑 (a*b))
    (nativeProjectiveChartRatioOpen_image 𝓑 a b ha hb)
  have h : ∀ x, E x = EW (T x) := by
    intro x
    have H := nativeSourceOverlapLocalizedSectionsLinearEquiv_eq_old 𝓑 𝒟 hD
      coords hcoords hgen a b ha hb hab hs
    exact congr($(H) x)
  constructor
  · intro x y hxy
    apply E.injective
    exact (h x).trans ((congrArg EW hxy).trans (h y).symm)
  · intro s
    let x := E.symm (EW s)
    refine ⟨x,EW.injective ?_⟩
    exact (h x).symm.trans (E.apply_symm_apply (EW s))
end LinearStudy
