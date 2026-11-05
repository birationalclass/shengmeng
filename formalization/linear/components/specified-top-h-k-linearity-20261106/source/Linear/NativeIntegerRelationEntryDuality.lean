module
public import Linear.NativeIntegerRelationLowEntryDuality
public import Linear.NativeIntegerRelationHighEntryTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ t : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z t →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w t)

/-- Dualizing the PROVED ORIGINAL coefficient entry transport gives the
actual original transpose square. Its polynomial,integer pieces and
maps are all ORIGINAL;no transpose identity is a premise. -/
theorem coordinateIntegerHighRelationDualEntry_transport (i : I) (j : J) (a b : ℕ)
    (hi : z i=(a:ℤ)+Fintype.card σ) (hj : w j=(b:ℤ)+Fintype.card σ) :
    projectiveHomogeneousGradedPolynomialDualEntry a b
      (coordinateIntegerHighRelationPolynomial z w c hc i j a b hi hj) ≫
      (projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj).dualMap.toModuleIso.hom =
    (projectiveHighIntegerWeightPieceEquiv (K := K) (z i) a hi).dualMap.toModuleIso.hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualRelationEntry (homogeneousSubmodule σ K)
        z w c hc (-(Fintype.card σ:ℤ)) i j).hom.dualMap := by
  rw [← projectiveHomogeneousGradedPolynomialMultiplyEntry_dual]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro q
  change φ (projectiveHomogeneousGradedPolynomialMultiplyEntry a b
    (coordinateIntegerHighRelationPolynomial z w c hc i j a b hi hj)
    (projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj q)) =
    φ (projectiveHighIntegerWeightPieceEquiv (K := K) (z i) a hi
      (LinearStudy.integerShiftedFreeDualRelationEntry (homogeneousSubmodule σ K)
        z w c hc (-(Fintype.card σ:ℤ)) i j q))
  have ht := congrArg (fun f => f (projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj q))
    (coordinateIntegerHighRelationCoefficientEntry_transport z w c hc i j a b hi hj)
  change projectiveHighIntegerWeightPieceEquiv (K := K) (z i) a hi
    (LinearStudy.integerShiftedFreeDualRelationEntry (homogeneousSubmodule σ K)
      z w c hc (-(Fintype.card σ:ℤ)) i j
      ((projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj).symm
        (projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj q))) = _ at ht
  rw [LinearEquiv.symm_apply_apply] at ht
  exact congrArg φ ht.symm

/-- The ORIGINAL scalar/Delta-entry square in the ACTUAL all-integer
free comparison,when the two selected weights are high. Other original
weights are arbitrary integers. All transports and polynomial squares
are PROVED and applied to the actual original entries. -/
theorem coordinateNativeIntegerRelationEntry_duality_of_high
    (i : I) (j : J) (hi : (Fintype.card σ:ℤ)≤z i)
    (hj : (Fintype.card σ:ℤ)≤w j) (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry
          (homogeneousSubmodule σ K) z w c hc i j)) ≫
      (coordinateNativeIntegerWeightHomDualIso (w j) n hcard).hom =
    (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualRelationEntry
        (homogeneousSubmodule σ K) z w c hc (-(Fintype.card σ:ℤ)) i j).hom.dualMap := by
  let a := (z i-(Fintype.card σ:ℤ)).toNat
  let b := (w j-(Fintype.card σ:ℤ)).toNat
  have ha : z i=(a:ℤ)+Fintype.card σ := by dsimp [a]; omega
  have hb : w j=(b:ℤ)+Fintype.card σ := by dsimp [b]; omega
  let iz := coordinateNativeHighIntegerWeightSheafIso (K := K) (z i) a ha
  let iw := coordinateNativeHighIntegerWeightSheafIso (K := K) (w j) b hb
  let p := coordinateIntegerHighRelationPolynomial z w c hc i j a b ha hb
  let e := LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry (homogeneousSubmodule σ K) z w c hc i j
  let u := LinearStudy.integerShiftedFreeDualRelationEntry (homogeneousSubmodule σ K)
    z w c hc (-(Fintype.card σ:ℤ)) i j
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let dz := (projectiveHighIntegerWeightPieceEquiv (K := K) (z i) a ha).dualMap.toModuleIso.hom
  let dw := (projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hb).dualMap.toModuleIso.hom
  have hs := congrArg G.map (coordinateIntegerHighRelationSheafEntry_transport z w c hc i j a b ha hb)
  simp only [Functor.map_comp] at hs
  have hg : G.map e ≫ G.map iw.hom = G.map iz.hom ≫
      G.map (coordinateNativeGradedPolynomialEntry a b p) :=
    (G.mapIso iz).inv_comp_eq.mp (by
      simpa only [Functor.mapIso_inv,Category.assoc] using hs)
  have hn := coordinateNativeCanonicalTopHomologyDualIso_polynomial a b n hcard p
  change G.map (coordinateNativeGradedPolynomialEntry a b p) ≫
    (coordinateNativeCanonicalTopHomologyDualIso b n hcard).hom =
    (coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫
      projectiveHomogeneousGradedPolynomialDualEntry a b p at hn
  have hd := coordinateIntegerHighRelationDualEntry_transport z w c hc i j a b ha hb
  change projectiveHomogeneousGradedPolynomialDualEntry a b p ≫ dw =
    dz ≫ ModuleCat.ofHom u.hom.dualMap at hd
  rw [coordinateNativeIntegerWeightHomDualIso_high_factor (w j) b hb,
    coordinateNativeIntegerWeightHomDualIso_high_factor (z i) a ha]
  change G.map e ≫ G.map iw.hom ≫
    (coordinateNativeCanonicalTopHomologyDualIso b n hcard).hom ≫ dw =
    G.map iz.hom ≫ (coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫ dz ≫
      ModuleCat.ofHom u.hom.dualMap
  calc
    _ = (G.map e ≫ G.map iw.hom) ≫
        ((coordinateNativeCanonicalTopHomologyDualIso b n hcard).hom ≫ dw) := by
      simp only [Category.assoc]
    _ = (G.map iz.hom ≫ G.map (coordinateNativeGradedPolynomialEntry a b p)) ≫
        ((coordinateNativeCanonicalTopHomologyDualIso b n hcard).hom ≫ dw) := by rw [hg]
    _ = G.map iz.hom ≫
        (G.map (coordinateNativeGradedPolynomialEntry a b p) ≫
          (coordinateNativeCanonicalTopHomologyDualIso b n hcard).hom) ≫ dw := by
      simp only [Category.assoc]
    _ = G.map iz.hom ≫
        ((coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫
          projectiveHomogeneousGradedPolynomialDualEntry a b p) ≫ dw := by rw [hn]
    _ = G.map iz.hom ≫ (coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫
        (projectiveHomogeneousGradedPolynomialDualEntry a b p ≫ dw) := by
      simp only [Category.assoc]
    _ = G.map iz.hom ≫ (coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫
        (dz ≫ ModuleCat.ofHom u.hom.dualMap) := by rw [hd]
    _ = _ := by simp only [Category.assoc]

/-- For EVERY ORIGINAL INTEGER weight pair,the ACTUAL ORIGINAL sheaf
relation entry and ACTUAL ORIGINAL Delta coefficient transpose commute
with the CONSTRUCTED all-integer free Cech/Hom comparison. This includes
negative/intermediate twists and original negative-degree zero entries.
No entry/matrix/duality comparison is assumed. Whole presentation remains separate. -/
theorem coordinateNativeIntegerRelationEntry_duality
    (i : I) (j : J) (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry
          (homogeneousSubmodule σ K) z w c hc i j)) ≫
      (coordinateNativeIntegerWeightHomDualIso (w j) n hcard).hom =
    (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualRelationEntry
        (homogeneousSubmodule σ K) z w c hc (-(Fintype.card σ:ℤ)) i j).hom.dualMap := by
  by_cases hi : (Fintype.card σ:ℤ)≤z i
  · by_cases hj : (Fintype.card σ:ℤ)≤w j
    · exact coordinateNativeIntegerRelationEntry_duality_of_high z w c hc i j hi hj n hcard
    · exact coordinateNativeIntegerRelationEntry_duality_of_target_lt z w c hc i j
        (lt_of_not_ge hj) n hcard
  · exact coordinateNativeIntegerRelationEntry_duality_of_source_lt z w c hc i j
      (lt_of_not_ge hi) n hcard

end MvPolynomial
