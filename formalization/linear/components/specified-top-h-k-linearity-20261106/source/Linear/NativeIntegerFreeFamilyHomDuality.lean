module
public import Linear.NativeIntegerFreeHomDuality
public import Linear.IntegerShiftedFreeHomPiCoordinates
public import Linear.FiniteBiproductDualCoordinates
public import Linear.NativeShiftedFreeSheafBiproductMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits

/-- Actual biproduct preservation sends the ORIGINAL inclusion to the
ORIGINAL mapped inclusion. Uses the original projection identities. -/
theorem functorBiproductMap_inclusion {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {I : Type} (f : I → C) [HasBiproduct f] [PreservesBiproduct f F]
    [HasBiproduct (F.obj ∘ f)] (i : I) :
    F.map (biproduct.ι f i) ≫ (F.mapBiproduct f).hom = biproduct.ι (F.obj ∘ f) i := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc,Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]
  rw [← F.map_comp]
  by_cases h : i=j
  · subst j
    simp only [biproduct.ι_π_self]
    exact F.map_id (f i)
  · rw [biproduct.ι_π_ne f h,biproduct.ι_π_ne (F.obj ∘ f) h,Functor.map_zero]

end LinearStudy

namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {I : Type} [Fintype I] [DecidableEq I]

/-- For EVERY ORIGINAL finite family of INTEGER weights,the ACTUAL
original shifted-free associated sheaf has top ordered-Cech homology
canonically dual to the ORIGINAL degree -N Hom-coordinate tuple.
Uses the constructed original free bicone,actual additive functors,
proved all-integer single-cell comparisons,and original finite dual and
Submodule.pi coordinates. No family duality comparison is an input. -/
def coordinateNativeIntegerFreeFamilyCoefficientDualIso (w : I → ℤ)
    (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w)
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w) 0)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerShiftedFreeDualCoordinatePiece (homogeneousSubmodule σ K)
        w (-(Fintype.card σ:ℤ)))) := by
  let H := coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let G := H ⋙ F
  let f := fun i => coordinateNativeIntegerTwist (K := K) (σ := σ) (-w i)
  letI : HasBiproduct f := LinearStudy.nativeShiftedFreeHasBiproduct (homogeneousSubmodule σ K) w
  exact (G.mapIso (LinearStudy.nativeShiftedFreeSheafBiproductIso (homogeneousSubmodule σ K) w)).trans
    ((G.mapBiproduct f).trans
      ((biproduct.mapIso (fun i => coordinateNativeIntegerWeightHomDualIso (w i) n hcard)).trans
        ((LinearStudy.finiteBiproductDualIso (fun i => ModuleCat.of K
          (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
            (w i-(Fintype.card σ:ℤ))))).trans
          (LinearStudy.integerShiftedFreeDualCoordinatePiEquiv (homogeneousSubmodule σ K)
            w (-(Fintype.card σ:ℤ))).dualMap.toModuleIso)))

/-- The all-integer actual free comparison preserves the ORIGINAL
single-coordinate sheaf inclusion and original finite dual inclusion.
This is a proved original map identity,not just a family isomorphism. -/
theorem coordinateNativeIntegerFreeFamilyCoefficientDualIso_inclusion
    (w : I → ℤ) (n : ℕ) (hcard : Fintype.card σ=n+2) (i : I) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeShiftedFreeCoordinateSheafInclusion (homogeneousSubmodule σ K) w i)) ≫
      (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard).hom =
    (coordinateNativeIntegerWeightHomDualIso (w i) n hcard).hom ≫
      biproduct.ι (fun j => ModuleCat.of K (Module.Dual K
        (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
          (w j-(Fintype.card σ:ℤ))))) i ≫
      (LinearStudy.finiteBiproductDualIso (fun j => ModuleCat.of K
        (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
          (w j-(Fintype.card σ:ℤ))))).hom ≫
      (LinearStudy.integerShiftedFreeDualCoordinatePiEquiv (homogeneousSubmodule σ K)
        w (-(Fintype.card σ:ℤ))).dualMap.toModuleIso.hom := by
  let H := coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let G := H ⋙ F
  let f := fun j => coordinateNativeIntegerTwist (K := K) (σ := σ) (-w j)
  letI : HasBiproduct f := LinearStudy.nativeShiftedFreeHasBiproduct (homogeneousSubmodule σ K) w
  have hi : LinearStudy.nativeShiftedFreeCoordinateSheafInclusion (homogeneousSubmodule σ K) w i ≫
      (LinearStudy.nativeShiftedFreeSheafBiproductIso (homogeneousSubmodule σ K) w).hom =
        biproduct.ι f i := by
    rw [← LinearStudy.nativeShiftedFreeSheafBiproductIso_inclusion]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rfl
  unfold coordinateNativeIntegerFreeFamilyCoefficientDualIso
  simp only [Iso.trans_hom,Functor.mapIso_hom,biproduct.mapIso_hom]
  change G.map (LinearStudy.nativeShiftedFreeCoordinateSheafInclusion (homogeneousSubmodule σ K) w i) ≫
    G.map (LinearStudy.nativeShiftedFreeSheafBiproductIso (homogeneousSubmodule σ K) w).hom ≫
    (G.mapBiproduct f).hom ≫ _ = _
  rw [← Category.assoc,← G.map_comp,hi]
  erw [← Category.assoc,LinearStudy.functorBiproductMap_inclusion]
  simpa only [Category.assoc,biproduct.ι_map_assoc]

end MvPolynomial
