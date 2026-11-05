module
public import Linear.OrderedToFullFreeFormalCech
public import Linear.ChainZeroHomologySameRelations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicTopology
open AlgebraicGeometry.Scheme.Modules
universe u
/-- The SAME native full Cech chains of actual free-open presheaves. -/
def fullFreeAbelianPresheafComplex (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :
    ChainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (alternatingFaceMapComplex _).obj
    ((FormalCoproduct.mk _ U).cech ⋙ orderedFreeOpenFormalPresheafFunctor X)
def fullFreePresheafValueChain (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) (V : X.Opens) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  (fullFreeAbelianPresheafComplex X U).asFunctor.obj (op V)
/-- Actual ordered-to-full comparison before exact sheafification. -/
def orderedToFullFreePresheafChain (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : orderedFreeAbelianPresheafComplex X U ⟶
      fullFreeAbelianPresheafComplex X U :=
  orderedToFullFormalCechChain (orderedFreeOpenFormalPresheafFunctor X) U
def orderedToFullFreePresheafValueChain (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) : orderedFreePresheafValueChain X U V ⟶
      fullFreePresheafValueChain X U V :=
  (((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)).mapHomologicalComplex (.down ℕ)).map
    (orderedToFullFreePresheafChain X U)
instance orderedToFullFreePresheafValueChain_zero_isIso (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (V : X.Opens) :
    IsIso ((orderedToFullFreePresheafValueChain X U V).f 0) := by
  change IsIso (((orderedFreeOpenFormalPresheafFunctor X).map
    (orderedCechFormalInclusion U 0)).app (op V))
  infer_instance
/-- Full and ordered differentials use precisely the SAME original faces and signs. -/
theorem fullFreePresheafValueChain_d (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ) :
    (fullFreePresheafValueChain X U V).d (n+1) n =
      ∑ k : Fin (n+2),(-1 : ℤ) ^ (k : ℕ) •
        ((orderedFreeOpenFormalPresheafFunctor X).map ((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun)).app (op V) := by
  change ((fullFreeAbelianPresheafComplex X U).d (n+1) n).app (op V) = _
  simp only [fullFreeAbelianPresheafComplex,alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD]
  change (∑ k : Fin (n+2),(-1 : ℤ) ^ (k : ℕ) •
    (orderedFreeOpenFormalPresheafFunctor X).map ((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun)).app (op V) = _
  simp only [NatTrans.app_sum,NatTrans.app_zsmul]
/-- Full native presheaf Cech augmentation,transported along the ACTUAL simplicial
isomorphism,proves positive exactness before any cover assumption. -/
theorem fullFreeAbelianPresheafComplex_positive_exact (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (p : ℕ) :
    (fullFreeAbelianPresheafComplex X U).ExactAt (p+1) := by
  let P := topCechFreeAbelianPresheafAugmented X U
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app P) :=
    (FormalCoproduct.mk _ U).shrinkYonedaCech_presheaf_augmentation_quasiIso AddCommGrpCat.free
  have hP := (exactAt_iff_of_quasiIsoAt (AlternatingFaceMapComplex.ε.app P) (p+1)).mpr
    (ChainComplex.exactAt_succ_single_obj P.right p)
  exact hP.of_iso ((alternatingFaceMapComplex _).mapIso (topCechFreePresheafSimplicialIso X U))
/-- On a finite ordered vertex type,ANY degree-zero constant cocycle has equal
values on ANY two vertices;no nonempty vertex assumption is needed. -/
theorem orderedConstantCech_zero_cocycle_eq {ι : Type u} [LinearOrder ι] [Finite ι]
    {M : Type u} [AddCommGroup M] (s : OrderedCechIndex ι 0 → M)
    (hs : ∀ a,orderedConstantCechDifferential 0 s a = 0) (a b : OrderedCechIndex ι 0) :
    s a = s b := by
  classical
  letI : Nonempty ι := ⟨a.1 0⟩
  letI := Fintype.ofFinite ι
  letI := Fintype.toOrderBot ι
  obtain ⟨m,hm⟩ := orderedConstantCech_zero_cocycle_constant s hs
  exact (hm a).trans (hm b).symm
end LinearStudy
