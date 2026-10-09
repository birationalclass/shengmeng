module
public import Linear.NativeProjectiveTwistChartFree
public import Linear.NativeProjectiveDegreeOneCover
public import Linear.SheafFreeIsoGenerators
public import Mathlib.CategoryTheory.Sites.Spaces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Actual local rank-one generators over an actual degree-one chart cover. -/
def nativePositiveTwistLocalGeneratorsData {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (m : ℕ)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).LocalGeneratorsData where
  I := ι
  X i := Proj.basicOpen 𝓑 (a i)
  coversTop := (Opens.coversTop_iff _ _).mpr hcover
  generators i :=
    (SheafOfModules.free.generatingSections
      (R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over (Proj.basicOpen 𝓑 (a i)))
      PUnit.{u+1}).ofEpi
        (nativePositiveTwistChartFreeIso 𝓑 (a i) (ha i) m
          (Proj.basicOpen 𝓑 (a i)) (fun p => p.2)).hom

/-- The actual native chart generators are locally free data: every
presentation map is the genuine constructed rank-one isomorphism. -/
theorem nativePositiveTwistLocalGeneratorsData_isLocallyFreeData
    {ι : Type u} (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1) (m : ℕ)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativePositiveTwistLocalGeneratorsData 𝓑 a ha m hcover).IsLocallyFreeData := by
  constructor
  intro i
  exact freeIsoGeneratingSections_isIso
    (nativePositiveTwistChartFreeIso 𝓑 (a i) (ha i) m
      (Proj.basicOpen 𝓑 (a i)) (fun p => p.2))

/-- The positive twist on an actual degree-one generated native Proj is
locally free, deduced from actual fractions and the proved chart cover. -/
theorem nativePositiveTwist_isLocallyFree {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (hgen : Algebra.adjoin K (Set.range a) = ⊤) (m : ℕ) :
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).IsLocallyFree := by
  let q := nativePositiveTwistLocalGeneratorsData 𝓑 a ha m
    (degreeOneGenerated_nativeProj_cover 𝓑 a ha hgen)
  let : q.IsLocallyFreeData :=
    nativePositiveTwistLocalGeneratorsData_isLocallyFreeData 𝓑 a ha m _
  exact q.isLocallyFree

/-- Quasicoherence of the actual native positive twist follows from
the constructed local-free data rather than an input coherent model. -/
theorem nativePositiveTwist_isQuasicoherent {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (hgen : Algebra.adjoin K (Set.range a) = ⊤) (m : ℕ) :
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).IsQuasicoherent := by
  let := nativePositiveTwist_isLocallyFree 𝓑 a ha hgen m
  infer_instance

end LinearStudy
