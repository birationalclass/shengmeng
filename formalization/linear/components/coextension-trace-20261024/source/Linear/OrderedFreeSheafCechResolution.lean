module
public import Linear.FullCechZeroRelations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicTopology
universe u
/-- Actual ordered-to-full comparison has the SAME degree-zero cohomology. -/
theorem orderedToFullFreePresheafValue_quasiIsoAt_zero (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (V : X.Opens) :
    QuasiIsoAt (orderedToFullFreePresheafValueChain X U V) 0 :=
  chain_quasiIsoAt_zero_of_same_relations (orderedToFullFreePresheafValueChain X U V)
    (fun M h hh => fullFreePresheafValue_zero_relations X U V M h hh)
/-- The SAME actual ordered/free PRESHEAF complex is quasi-isomorphic to the SAME
native full/free complex.For a finite original family,this is proved at degree zero
by actual relations,and at positive degrees by actual exactness.No Cech/H premise. -/
theorem orderedToFullFreePresheafChain_quasiIso (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) :
    QuasiIso (orderedToFullFreePresheafChain X U) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    apply (HomologicalComplex.quasiIsoAt_iff_evaluation _ 0).mpr
    intro V
    exact orderedToFullFreePresheafValue_quasiIsoAt_zero X U V.unop
  | succ p =>
    exact (quasiIsoAt_iff_exactAt _ (p+1)
      (orderedFreeAbelianPresheafComplex_positive_exact X U p)).mpr
        (fullFreeAbelianPresheafComplex_positive_exact X U p)
/-- The actual ordered/free SHEAF complex obtained by exact sheafification. -/
def orderedFreeAbelianSheafComplex (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.down ℕ)).obj (orderedFreeAbelianPresheafComplex X U)
/-- Compare the actual ordered/free SHEAF chains to the original native full SHEAF
Cech chains,using native presheaf and exact-sheafification comparison isomorphisms. -/
def orderedToNativeFullFreeSheafChain (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : orderedFreeAbelianSheafComplex X U ⟶
      (alternatingFaceMapComplex _).obj (topCechFreeAbelianAugmented X U).left := by
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let e := (alternatingFaceMapComplex _).mapIso (topCechFreePresheafSimplicialIso X U)
  exact (S.mapHomologicalComplex (.down ℕ)).map
    (orderedToFullFreePresheafChain X U ≫ e.inv) ≫
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso S).app
        (topCechFreeAbelianPresheafAugmented X U).left).hom
/-- The ACTUAL ordered-to-native-full free SHEAF comparison is a quasi-isomorphism. -/
theorem orderedToNativeFullFreeSheafChain_quasiIso (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) :
    QuasiIso (orderedToNativeFullFreeSheafChain X U) := by
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let e := (alternatingFaceMapComplex _).mapIso (topCechFreePresheafSimplicialIso X U)
  let eS := (alternatingFaceMapComplexCompMapHomologicalComplexIso S).app
    (topCechFreeAbelianPresheafAugmented X U).left
  letI : QuasiIso (orderedToFullFreePresheafChain X U) :=
    orderedToFullFreePresheafChain_quasiIso X U
  letI : QuasiIso e.inv := quasiIso_of_isIso _
  letI : QuasiIso (orderedToFullFreePresheafChain X U ≫ e.inv) := quasiIso_comp _ _
  letI : QuasiIso ((S.mapHomologicalComplex (.down ℕ)).map
      (orderedToFullFreePresheafChain X U ≫ e.inv)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ S
  letI : QuasiIso eS.hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _
/-- The SAME actual finite ORDERED free-SHEAF complex is augmented to the SAME
native constant lifted-integer SHEAF which defines native sheaf cohomology. -/
def orderedCechNativeIntegerAugmentation (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : orderedFreeAbelianSheafComplex X U ⟶
      (ChainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  orderedToNativeFullFreeSheafChain X U ≫ topCechNativeIntegerAugmentation X U
/-- An ACTUAL finite ordered open cover gives an actual quasi-isomorphic ORDERED
free-SHEAF resolution of the SAME native integer SHEAF.No Serre,duality or desired
cohomology-vanishing input is assumed. -/
theorem orderedCechNativeIntegerAugmentation_quasiIso (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) : QuasiIso (orderedCechNativeIntegerAugmentation X U) := by
  letI := orderedToNativeFullFreeSheafChain_quasiIso X U
  letI := topCechNativeIntegerAugmentation_quasiIso X U hU
  unfold orderedCechNativeIntegerAugmentation
  infer_instance
end LinearStudy
