module
public import Linear.NativeProjectiveShiftedFreeBiproduct
public import Linear.NativeProjectiveOverCokernel
public import Linear.NativeProjectiveIntegerTwistChartFree
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq ι] (w : ι → ℤ)

/-- Actual finite shifted free modules have an actual free associated
sheaf chart on every original degree-one basic open. -/
def nativeShiftedFreeChartIso [Fintype ι]
    (a : S) (ha : a ∈ 𝓑 1) (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    SheafOfModules.free (R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U) ι ≅
      (nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0).over U := by
  let F := SheafOfModules.overFunctor (AlgebraicGeometry.Proj 𝓑).ringCatSheaf U
  let G := fun i : ι => nativeProjectiveModuleSheaf 𝓑
    (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i)
  let H := fun _ : ι => SheafOfModules.unit ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.over U)
  letI : HasBiproduct G := nativeShiftedFreeHasBiproduct 𝓑 w
  letI : F.Additive := nativeSheafOverFunctor_additive 𝓑 U
  letI : HasBiproduct H := HasBiproduct.of_hasCoproduct H
  letI : PreservesBiproduct G F := {
    preserves := fun hb => ⟨isBilimitOfTotal _ (by
        simp_rw [F.mapBicone_π, F.mapBicone_ι, ← CategoryTheory.Functor.map_comp]
        erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ }
  letI : HasBiproduct (F.obj ∘ G) := inferInstance
  let e := F.mapIso (nativeShiftedFreeSheafBiproductIso 𝓑 w) ≪≫ F.mapBiproduct G
  let e' : biproduct (F.obj ∘ G) ≅ biproduct H := biproduct.mapIso
    (fun i : ι => (nativeIntegerTwistChartUnitIso 𝓑 a ha (-w i) U hp).symm)
  exact (e ≪≫ e' ≪≫ biproduct.isoCoproduct H).symm

end LinearStudy
