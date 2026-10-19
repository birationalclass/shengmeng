module
public import Linear.AlternatingHomOppositeComplex
public import Linear.InjectiveHomResolutionAcyclic
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology TopologicalSpace Opposite
universe u
namespace LinearStudy
/-- For an ACTUAL injective ABELIAN SHEAF,the original full native Cech complex
is exact in EVERY positive degree,for ANY actual open cover.
No affine,Cech/native-H comparison,or desired-acyclicity premise is supplied. -/
theorem topInjectiveAbelianSheaf_nativeCech_exactAt (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n+1) := by
  let A := TopCat.Sheaf AddCommGrpCat.{u} X
  let K := (alternatingFaceMapComplex A).obj (topCechFreeAbelianAugmented X U).left
  let Z := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let H := preadditiveYoneda.obj F
  let f := topCechNativeIntegerAugmentation X U
  letI : QuasiIso f := topCechNativeIntegerAugmentation_quasiIso X U hU
  have ht : ((H.mapHomologicalComplex (.up ℕ)).obj K.op).ExactAt (n+1) :=
    injectiveHomOppositeOfResolution_exactAt K Z f F n
  exact ht.of_iso (alternatingHomCochainIso (topCechFreeAbelianAugmented X U).left H ≪≫
    topCechFreeSheafHomComplexIso X U F)

/-- The ACTUAL positive homology objects of the original native full Cech complex
vanish for injective ABELIAN SHEAVES. This is not an O-module injectivity claim. -/
theorem topInjectiveAbelianSheaf_nativeCech_positiveHomology_isZero (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    IsZero (((cechComplexFunctor U).obj F.obj).homology (n+1)) :=
  (topInjectiveAbelianSheaf_nativeCech_exactAt X U hU F n).isZero_homology
end LinearStudy
