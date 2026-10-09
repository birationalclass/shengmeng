module
public import Linear.NativeProjectiveTwistChartFree
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

/-- Every actual integer twist is trivial on an actual degree-one chart.
The negative case inverts the already constructed multiplication-by-a-power
isomorphism, rather than assuming a line bundle presentation. -/
def nativeIntegerTwistChartUnitIso (a : S) (ha : a ∈ 𝓑 1) (k : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    SheafOfModules.unit ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U) ≅
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k).over U := by
  cases k with
  | ofNat n => exact nativePositiveTwistChartUnitIso 𝓑 a ha n U hp
  | negSucc n =>
    have h : Int.negSucc n + ((n + 1 : ℕ) : ℤ) = 0 := by omega
    have e := nativeProjectiveTwistSheafOverIso 𝓑 a ha (n + 1) (Int.negSucc n) U hp
    rw [h] at e
    exact nativePositiveTwistChartUnitIso 𝓑 a ha 0 U hp ≪≫ e.symm

/-- Rank-one free chart presentation of the actual associated module
sheaf of any integer twist. -/
def nativeIntegerTwistChartFreeIso (a : S) (ha : a ∈ 𝓑 1) (k : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    SheafOfModules.free (R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U)
      PUnit.{u+1} ≅
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k).over U :=
  (Limits.coproductUniqueIso (fun _ : PUnit.{u+1} =>
    SheafOfModules.unit ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U))) ≪≫
      nativeIntegerTwistChartUnitIso 𝓑 a ha k U hp

end LinearStudy
