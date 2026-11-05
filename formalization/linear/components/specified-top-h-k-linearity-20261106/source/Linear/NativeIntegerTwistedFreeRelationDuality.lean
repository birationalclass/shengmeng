module
public import Linear.NativeIntegerFreeTwistMapNaturality
public import Linear.IntegerShiftedFreeRelationDualRegrading
public import Linear.NativeIntegerTwistedFreeFamilyHomDuality
public import Linear.NativeIntegerFreeRelationMatrixDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w d)

/-- EVERY actual ORIGINAL integer free-family map commutes with the
CONSTRUCTED actual Cech/coordinate duality for EVERY integer k. Original
Delta at -N-k and original c are retained. Both original sheaf and
contravariant whole-matrix transports are proved,not assumed. -/
theorem coordinateNativeIntegerTwistedFreeRelation_duality (n : ℕ)
    (hcard : Fintype.card σ=n+2) (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w)
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) z)
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w) c hc k)) ≫
      (coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso w k n hcard).hom =
    (coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso z k n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c
        (homogeneousSubmodule σ K) z w hc (-(Fintype.card σ:ℤ)-k)).dualMap := by
  let B := homogeneousSubmodule σ K
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let zk := fun i => z i-k
  let wk := fun j => w j-k
  let hck := LinearStudy.integerShiftedFreeRelation_regrade B z w c hc k
  let γz := LinearStudy.nativeIntegerFreeTwistRegradingIso B z k
  let γw := LinearStudy.nativeIntegerFreeTwistRegradingIso B w k
  let e := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B z) (LinearStudy.integerShiftedFreePiece B w)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B z)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) c hc k
  let ek := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B zk) (LinearStudy.integerShiftedFreePiece B wk)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B zk)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wk) c hck 0
  let Φz := coordinateNativeIntegerFreeFamilyCoefficientDualIso (K := K) (σ := σ) zk n hcard
  let Φw := coordinateNativeIntegerFreeFamilyCoefficientDualIso (K := K) (σ := σ) wk n hcard
  let εz := (LinearStudy.integerShiftedFreeDualCoordinateRegradingEquiv B z k
    (-(Fintype.card σ:ℤ))).dualMap.toModuleIso
  let εw := (LinearStudy.integerShiftedFreeDualCoordinateRegradingEquiv B w k
    (-(Fintype.card σ:ℤ))).dualMap.toModuleIso
  let δk := ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix
    c B zk wk hck (-(Fintype.card σ:ℤ))).dualMap
  let δ := ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix
    c B z w hc (-(Fintype.card σ:ℤ)-k)).dualMap
  have hprimal : γz.inv ≫ ek ≫ γw.hom=e :=
    LinearStudy.nativeIntegerFreeTwistRegradingIso_map B z w c hc k
  have he : G.map e ≫ G.map γw.inv = G.map γz.inv ≫ G.map ek := by
    have h : e ≫ γw.inv = γz.inv ≫ ek := by
      rw [← hprimal]
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rw [← G.map_comp,h,G.map_comp]
  have hrelation := coordinateNativeIntegerFreeRelation_duality zk wk c hck n hcard
  change G.map ek ≫ Φw.hom = Φz.hom ≫ δk at hrelation
  have hdual : δk ≫ εw.inv = εz.inv ≫ δ :=
    LinearStudy.integerShiftedFreeRelationDualMap_regrade B z w c hc k (-(Fintype.card σ:ℤ))
  change G.map e ≫ _ = _ ≫ δ
  calc
    G.map e ≫ (coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso w k n hcard).hom =
      (G.map e ≫ G.map γw.inv) ≫ Φw.hom ≫ εw.inv := by
        simp only [coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso,
          Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv,Category.assoc]
        rfl
    _ = G.map γz.inv ≫ (G.map ek ≫ Φw.hom) ≫ εw.inv := by
      rw [he]
      simp only [Category.assoc]
    _ = G.map γz.inv ≫ (Φz.hom ≫ δk) ≫ εw.inv := by rw [hrelation]
    _ = G.map γz.inv ≫ Φz.hom ≫ εz.inv ≫ δ := by
      simp only [Category.assoc]
      rw [hdual]
    _ = (coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso z k n hcard).hom ≫ δ := by rfl

end MvPolynomial
