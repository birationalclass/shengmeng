module
public import Linear.NativeIntegerRelationEntryDuality
public import Linear.IntegerShiftedFreeGeneralDualMatrix
public import Linear.BiproductMatrixNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ t : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z t →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w t)

/-- For EVERY ORIGINAL finite family of INTEGER weights,the ACTUAL
ORIGINAL whole sheafified relation c commutes with ORIGINAL Delta_-N*
under the CONSTRUCTED all-integer free comparisons. All original entries,
negative/intermediate twists,actual coefficient maps and finite dual
assembly are proved,not supplied as comparison assumptions.
This is WHOLE FREE RELATION naturality,not yet the whole M presentation. -/
theorem coordinateNativeIntegerFreeRelation_duality (n : ℕ)
    (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w)
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) z)
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w) c hc 0)) ≫
      (coordinateNativeIntegerFreeFamilyCoefficientDualIso w n hcard).hom =
    (coordinateNativeIntegerFreeFamilyCoefficientDualIso z n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c
        (homogeneousSubmodule σ K) z w hc (-(Fintype.card σ:ℤ))).dualMap := by
  let B := homogeneousSubmodule σ K
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let fz := fun i => coordinateNativeIntegerTwist (K := K) (σ := σ) (-z i)
  let fw := fun j => coordinateNativeIntegerTwist (K := K) (σ := σ) (-w j)
  letI : HasBiproduct fz := LinearStudy.nativeShiftedFreeHasBiproduct B z
  letI : HasBiproduct fw := LinearStudy.nativeShiftedFreeHasBiproduct B w
  let iz := LinearStudy.nativeShiftedFreeSheafBiproductIso B z
  let iw := LinearStudy.nativeShiftedFreeSheafBiproductIso B w
  let e := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B z) (LinearStudy.integerShiftedFreePiece B w)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B z)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) c hc 0
  let entries := LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry B z w c hc
  let dualEntries := fun i j => ModuleCat.ofHom
    (LinearStudy.integerShiftedFreeDualRelationEntry B z w c hc (-(Fintype.card σ:ℤ)) i j).hom.dualMap
  let cz := LinearStudy.integerShiftedFreeDegreeCoefficientDualIso B z (-(Fintype.card σ:ℤ))
  let cw := LinearStudy.integerShiftedFreeDegreeCoefficientDualIso B w (-(Fintype.card σ:ℤ))
  have hm := congrArg G.map (LinearStudy.nativeShiftedFreeSheafMap_scalarMatrix B z w c hc)
  simp only [Functor.map_comp] at hm
  have hg : G.map e ≫ G.map iw.hom = G.map iz.hom ≫ G.map (biproduct.matrix entries) :=
    (G.mapIso iz).inv_comp_eq.mp (by simpa only [Functor.mapIso_inv,Category.assoc] using hm)
  have hb := LinearStudy.additiveFunctorBiproductMatrixNaturality G entries
  have hs := LinearStudy.biproductMatrixComponentNaturality
    (fun i j => G.map (entries i j)) dualEntries
    (fun i => (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom)
    (fun j => (coordinateNativeIntegerWeightHomDualIso (w j) n hcard).hom)
    (fun i j => coordinateNativeIntegerRelationEntry_duality z w c hc i j n hcard)
  have hd := LinearStudy.integerShiftedFreeDegreeRelationDual_matrix B z w c hc (-(Fintype.card σ:ℤ))
  unfold coordinateNativeIntegerFreeFamilyCoefficientDualIso
  simp only [Iso.trans_hom,Functor.mapIso_hom,biproduct.mapIso_hom]
  change G.map e ≫ G.map iw.hom ≫ (G.mapBiproduct fw).hom ≫
    biproduct.map (fun j => (coordinateNativeIntegerWeightHomDualIso (w j) n hcard).hom) ≫ cw.hom =
    G.map iz.hom ≫ (G.mapBiproduct fz).hom ≫
      biproduct.map (fun i => (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom) ≫
      cz.hom ≫ ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c B z w hc
        (-(Fintype.card σ:ℤ))).dualMap
  rw [← Category.assoc,hg]
  simp only [Category.assoc]
  apply congrArg (fun t => G.map iz.hom ≫ t)
  rw [← Category.assoc,hb]
  simp only [Category.assoc]
  apply congrArg (fun t => (G.mapBiproduct fz).hom ≫ t)
  erw [← Category.assoc,hs]
  simp only [Category.assoc]
  apply congrArg (fun t => biproduct.map
    (fun i => (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom) ≫ t)
  exact hd

end MvPolynomial
