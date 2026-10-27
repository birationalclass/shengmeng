module
public import Linear.TopFormalFreePresheafValueHom
public import Linear.OrderedContainedCechTuples
public import Linear.OrderedConstantCechFiniteContraction
public import Linear.ChainExactOfAllHomExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- Reindex coefficient functions by a PROVED equivalence of actual generators. -/
def functionReindexAddEquiv {T S : Type u} (e : T ≃ S) (M : AddCommGrpCat.{u}) :
    (T → M) ≃+ (S → M) where
  toFun s a := s (e.symm a)
  invFun s a := s (e a)
  left_inv s := by funext a; simp
  right_inv s := by funext a; simp
  map_add' s t := rfl
/-- Evaluation of the SAME actual ordered free-presheaf chains. -/
def orderedFreePresheafValueChain (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (orderedFreeAbelianPresheafComplex X U).asFunctor.obj (op V)
/-- Actual Hom cochains are precisely ordered constant-coefficient functions on
indices containing V.This states a degreewise additive equivalence. -/
def orderedFreeValueHomCoefficients (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (M : AddCommGrpCat.{u}) (n : ℕ) :
    ((orderedFreePresheafValueChain X U V).X n ⟶ M) ≃+
      (OrderedCechIndex (coverIndicesContainingOpen U V) n → M) :=
  (topFormalFreeValueHomAddEquiv X V M (orderedCechFormalObject U n)).trans
    (functionReindexAddEquiv (orderedCechTupleSectionEquiv U V n) M)
/-- The evaluated chain differential retains EVERY original face and integer sign. -/
theorem orderedFreePresheafValueChain_d (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ) :
    (orderedFreePresheafValueChain X U V).d (n+1) n =
      ∑ k : Fin (n+2),(-1 : ℤ) ^ (k : ℕ) •
        ((orderedFreeOpenFormalPresheafFunctor X).map (orderedCechFace U n k)).app (op V) := by
  change (((orderedFormalCechComplex (orderedFreeOpenFormalPresheafFunctor X).op U).d
    n (n+1)).unop).app (op V) = _
  rw [orderedFormalCechComplex_d]
  simp only [orderedFormalCechDifferential,unop_sum,unop_zsmul,
    orderedFormalCechCoface,Functor.op_map,Quiver.Hom.unop_op]
  simp
/-- The degreewise equivalence intertwines the ACTUAL differential with the SAME
original ordered constant-coefficient differential,including all signs. -/
theorem orderedFreeValueHomCoefficients_d (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (M : AddCommGrpCat.{u}) (n : ℕ)
    (h : (orderedFreePresheafValueChain X U V).X n ⟶ M)
    (a : OrderedCechIndex (coverIndicesContainingOpen U V) (n+1)) :
    orderedFreeValueHomCoefficients X U V M (n+1)
      ((orderedFreePresheafValueChain X U V).d (n+1) n ≫ h) a =
      orderedConstantCechDifferential n (orderedFreeValueHomCoefficients X U V M n h) a := by
  let x := (orderedCechTupleSectionEquiv U V (n+1)).symm a
  change topFormalFreeValueHomAddEquiv X V M (orderedCechFormalObject U (n+1))
    ((orderedFreePresheafValueChain X U V).d (n+1) n ≫ h) x = _
  rw [orderedFreePresheafValueChain_d]
  simp only [sum_comp,zsmul_comp,map_sum,map_zsmul,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [topFormalFreeValueHomAddEquiv_precomp]
  have hk : orderedCechTupleSectionDelete U V n k x =
      (orderedCechTupleSectionEquiv U V n).symm (a.delete k) := by
    apply (orderedCechTupleSectionEquiv U V n).injective
    rw [orderedCechTupleSectionEquiv_delete,Equiv.apply_symm_apply]
    rfl
  change (-1 : ℤ) ^ (k : ℕ) • topFormalFreeValueHomAddEquiv X V M
    (orderedCechFormalObject U n) h (orderedCechTupleSectionDelete U V n k x) = _
  rw [hk]
  rfl
end LinearStudy
