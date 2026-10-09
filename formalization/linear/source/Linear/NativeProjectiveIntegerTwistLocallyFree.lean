module
public import Linear.NativeProjectiveIntegerTwistChartFree
public import Linear.NativeProjectiveTwistLocallyFree
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

/-- Local-free generators of every actual integer twist over an actual
degree-one basic-open cover. -/
def nativeIntegerTwistLocalGeneratorsData {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (k : ℤ)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k).LocalGeneratorsData where
  I := ι
  X i := Proj.basicOpen 𝓑 (a i)
  coversTop := (Opens.coversTop_iff _ _).mpr hcover
  generators i :=
    (SheafOfModules.free.generatingSections
      (R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over (Proj.basicOpen 𝓑 (a i)))
      PUnit.{u+1}).ofEpi
        (nativeIntegerTwistChartFreeIso 𝓑 (a i) (ha i) k
          (Proj.basicOpen 𝓑 (a i)) (fun p => p.2)).hom

/-- The actual rank-one chart presentations are isomorphisms. -/
theorem nativeIntegerTwistLocalGeneratorsData_isLocallyFreeData
    {ι : Type u} (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1) (k : ℤ)
    (hcover : (⨆ i, Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeIntegerTwistLocalGeneratorsData 𝓑 a ha k hcover).IsLocallyFreeData := by
  constructor
  intro i
  exact freeIsoGeneratingSections_isIso
    (nativeIntegerTwistChartFreeIso 𝓑 (a i) (ha i) k
      (Proj.basicOpen 𝓑 (a i)) (fun p => p.2))

/-- All actual integer twists are locally free on a degree-one
generated native Proj, including negative twists. -/
theorem nativeIntegerTwist_isLocallyFree {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (hgen : Algebra.adjoin K (Set.range a) = ⊤) (k : ℤ) :
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k).IsLocallyFree := by
  let q := nativeIntegerTwistLocalGeneratorsData 𝓑 a ha k
    (degreeOneGenerated_nativeProj_cover 𝓑 a ha hgen)
  let : q.IsLocallyFreeData :=
    nativeIntegerTwistLocalGeneratorsData_isLocallyFreeData 𝓑 a ha k _
  exact q.isLocallyFree

/-- Quasicoherence of the actual integer twist follows from its
constructed local-free data. -/
theorem nativeIntegerTwist_isQuasicoherent {ι : Type u} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (hgen : Algebra.adjoin K (Set.range a) = ⊤) (k : ℤ) :
    (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k).IsQuasicoherent := by
  let := nativeIntegerTwist_isLocallyFree 𝓑 a ha hgen k
  infer_instance

end LinearStudy
