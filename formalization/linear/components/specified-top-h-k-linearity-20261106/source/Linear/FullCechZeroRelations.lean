module
public import Linear.FullFreePresheafValueCech
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Lift a SAME original full degree-zero generator to the ordered degree-zero basis. -/
def fullZeroCechGeneratorToOrdered (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens)
    (x : Σ a : Fin 1 → ι,ULift.{u} (V ⟶ ∏ᶜ fun k : Fin 1 => U (a k))) :
    orderedCechTupleSection U V 0 :=
  ⟨orderedCechDegreeZeroIndexEquiv.symm x.1,x.2⟩
/-- The actual comparison sends this generator to the SAME original generator. -/
theorem fullZeroCechGeneratorToOrdered_hom (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (M : AddCommGrpCat.{u})
    (h : (fullFreePresheafValueChain X U V).X 0 ⟶ M)
    (x : Σ a : Fin 1 → ι,ULift.{u} (V ⟶ ∏ᶜ fun k : Fin 1 => U (a k))) :
    topFormalFreeValueHomAddEquiv X V M (orderedCechFormalObject U 0)
      ((orderedToFullFreePresheafValueChain X U V).f 0 ≫ h)
        (fullZeroCechGeneratorToOrdered X U V x) =
      topFormalFreeValueHomAddEquiv X V M ((FormalCoproduct.mk _ U).power (Fin 1)) h x := by
  change (((orderedFreeOpenFormalPresheafFunctor X).obj
    ((FormalCoproduct.mk _ U).power (Fin 1))).obj (op V) ⟶ M) at h
  change topFormalFreeValueHomAddEquiv X V M (orderedCechFormalObject U 0)
    (((orderedFreeOpenFormalPresheafFunctor X).map (orderedCechFormalInclusion U 0)).app (op V) ≫ h)
      (fullZeroCechGeneratorToOrdered X U V x) = _
  refine (topFormalFreeValueHomAddEquiv_precomp X V M (orderedCechFormalInclusion U 0)
    h (fullZeroCechGeneratorToOrdered X U V x)).trans ?_
  simp only [fullZeroCechGeneratorToOrdered,orderedCechFormalInclusion,
    orderedCechDegreeZeroIndexEquiv,Category.comp_id]
  rfl
/-- Killing original ORDERED pair relations kills ALL original pair relations.
The actual source,target,intersections and coefficient object are preserved. -/
theorem fullFreePresheafValue_zero_relations (X : Scheme.{u})
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (V : X.Opens)
    (M : AddCommGrpCat.{u}) (h : (fullFreePresheafValueChain X U V).X 0 ⟶ M)
    (hh : (orderedFreePresheafValueChain X U V).d 1 0 ≫
      (orderedToFullFreePresheafValueChain X U V).f 0 ≫ h = 0) :
    (fullFreePresheafValueChain X U V).d 1 0 ≫ h = 0 := by
  change (((orderedFreeOpenFormalPresheafFunctor X).obj
    ((FormalCoproduct.mk _ U).power (Fin 1))).obj (op V) ⟶ M) at h
  let j := orderedToFullFreePresheafValueChain X U V
  let s := orderedFreeValueHomCoefficients X U V M 0 (j.f 0 ≫ h)
  have hs : ∀ a,orderedConstantCechDifferential 0 s a = 0 := by
    intro a
    rw [← orderedFreeValueHomCoefficients_d]
    rw [hh,map_zero]
    rfl
  have hv (y : orderedCechTupleSection U V 0) :
      s (orderedCechTupleSectionEquiv U V 0 y) =
        topFormalFreeValueHomAddEquiv X V M (orderedCechFormalObject U 0) (j.f 0 ≫ h) y := by
    change topFormalFreeValueHomAddEquiv X V M (orderedCechFormalObject U 0) (j.f 0 ≫ h)
      ((orderedCechTupleSectionEquiv U V 0).symm (orderedCechTupleSectionEquiv U V 0 y)) = _
    rw [Equiv.symm_apply_apply]
  have heq (x y : Σ a : Fin 1 → ι,ULift.{u} (V ⟶ ∏ᶜ fun k : Fin 1 => U (a k))) :
      topFormalFreeValueHomAddEquiv X V M ((FormalCoproduct.mk _ U).power (Fin 1)) h x =
        topFormalFreeValueHomAddEquiv X V M ((FormalCoproduct.mk _ U).power (Fin 1)) h y := by
    rw [← fullZeroCechGeneratorToOrdered_hom X U V M h x,
      ← fullZeroCechGeneratorToOrdered_hom X U V M h y,
      ← hv,← hv]
    exact orderedConstantCech_zero_cocycle_eq s hs _ _
  apply (topFormalFreeValueHomAddEquiv X V M ((FormalCoproduct.mk _ U).power (Fin 2))).injective
  funext x
  rw [fullFreePresheafValueChain_d]
  change topFormalFreeValueHomAddEquiv X V M ((FormalCoproduct.mk _ U).power (Fin 2))
    ((∑ k : Fin 2,(-1 : ℤ) ^ (k : ℕ) •
      ((orderedFreeOpenFormalPresheafFunctor X).map ((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun)).app (op V)) ≫ h) x = 0
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one,one_smul,
    neg_one_zsmul,add_comp,neg_comp,map_add,map_neg,map_zero,Pi.add_apply,Pi.neg_apply,Pi.zero_apply]
  rw [topFormalFreeValueHomAddEquiv_precomp,topFormalFreeValueHomAddEquiv_precomp]
  rw [← sub_eq_add_neg]
  exact sub_eq_zero.mpr (heq _ _)
end LinearStudy
