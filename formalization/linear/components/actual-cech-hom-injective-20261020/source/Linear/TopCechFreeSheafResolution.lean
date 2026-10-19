module
public import Linear.FormalCechPresheafResolution
public import Linear.TopCechIntegerTarget
public import Mathlib.Topology.Sheaves.Abelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology TopologicalSpace Opposite
universe u
namespace LinearStudy
/-- The ACTUAL augmented free-abelian SHEAF Cech object for the original opens.
Its n-th term comes from the actual formal coproduct of (n+1)-fold intersections. -/
def topCechFreeAbelianAugmented (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X) :
    SimplicialObject.Augmented (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (((SimplicialObject.Augmented.whiskering _ _).obj
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).obj
    (((SimplicialObject.Augmented.whiskering _ _).obj
      ((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
        AddCommGrpCat.free)).obj
      (FormalCoproduct.mk _ U).shrinkYonedaCech))

/-- Actual sheafification preserves the actual augmented quasi-isomorphism.
No cover hypothesis is needed until identifying its target with native integers. -/
theorem topCechFreeAbelianAugmented_quasiIso (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (topCechFreeAbelianAugmented X U)) := by
  let P := (((SimplicialObject.Augmented.whiskering _ _).obj
      ((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
        AddCommGrpCat.free)).obj
      (FormalCoproduct.mk _ U).shrinkYonedaCech)
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app P) :=
    (FormalCoproduct.mk _ U).shrinkYonedaCech_presheaf_augmentation_quasiIso
      AddCommGrpCat.free
  have h : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map
      (AlternatingFaceMapComplex.ε.app P)) := inferInstance
  exact ((HomologicalComplex.quasiIso _ (.down ℕ)).arrow_mk_iso_iff
    (alternatingAugmentationWhiskeringArrowIso P F)).mp h

/-- The SAME Cech free-sheaf complex,augmented to the native constant integer SHEAF. -/
def topCechNativeIntegerAugmentation (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) :
    (alternatingFaceMapComplex _).obj (topCechFreeAbelianAugmented X U).left ⟶
    (ChainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  AlternatingFaceMapComplex.ε.app (topCechFreeAbelianAugmented X U) ≫
    (ChainComplex.single₀ _).map (topCoverGeneratedFreeAbelianIntegerTargetMap X U)

/-- Every ACTUAL open cover gives a native quasi-isomorphic free-abelian SHEAF
Cech resolution of the SAME integer SHEAF which defines native sheaf cohomology. -/
theorem topCechNativeIntegerAugmentation_quasiIso (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U) :
    QuasiIso (topCechNativeIntegerAugmentation X U) := by
  letI := topCechFreeAbelianAugmented_quasiIso X U
  letI := topCoverGeneratedFreeAbelianIntegerTargetMap_isIso X U hU
  unfold topCechNativeIntegerAugmentation
  infer_instance
end LinearStudy
