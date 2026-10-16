module
public import Linear.NativeProjectiveTwistSheafOverIso
public import Linear.NativeStructureModuleSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
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

/-- The native structure module restricts to the structure module of
the actual native over-site. -/
def nativeStructureModuleOverUnitIso (U : Opens (ProjectiveSpectrum.top 𝓑)) :
    SheafOfModules.unit ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U) ≅
      (SheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf).over U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _)
      (by intros; apply ModuleCat.hom_ext; rfl))

/-- On an actual open where a degree-one element does not vanish, the
positive twist is genuinely isomorphic to the native structure module. -/
def nativePositiveTwistChartUnitIso (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)
    (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    SheafOfModules.unit ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U) ≅
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).over U := by
  simpa only [zero_add] using
    nativeStructureModuleOverUnitIso 𝓑 U ≪≫
    ((SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝓑).ringCatSheaf U).mapIso
      (nativeStructureRingZeroModuleSheafIso 𝓑)) ≪≫
        nativeProjectiveTwistSheafOverIso 𝓑 a ha m 0 U hp

/-- A rank-one free presentation on the actual native over-site,
constructed from the actual twist fraction isomorphism. -/
def nativePositiveTwistChartFreeIso (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)
    (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    SheafOfModules.free (R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U)
      PUnit.{u+1} ≅
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).over U :=
  (Limits.coproductUniqueIso (fun _ : PUnit.{u+1} =>
    SheafOfModules.unit ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U))) ≪≫
      nativePositiveTwistChartUnitIso 𝓑 a ha m U hp

end LinearStudy
