module
public import Linear.IntegerShiftedFreeNaturalRelationCoordinates
public import Linear.ProjectiveOriginalGradedPolynomialMultiply
public import Linear.FiniteBiproductMatrixDuality
public import Linear.NativePolynomialPresentationWeights
public import Linear.ProjectiveGradedDualCoefficientMatrix
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (a : I → ℕ) (b : J → ℕ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)

/-- The ACTUAL ORIGINAL degree-relation in its constructed original
natural polynomial piece coordinates,at original degree -card(sigma). -/
def coordinateOriginalNaturalRelationMap :
    (∀ j, homogeneousSubmodule σ K (b j)) →ₗ[K]
      (∀ i, homogeneousSubmodule σ K (a i)) :=
  LinearStudy.integerShiftedFreeNaturalDualRelationMatrix (homogeneousSubmodule σ K)
    (Fintype.card σ) a b c hc

/-- Put the original tuple relation into ORIGINAL ModuleCat biproduct
coordinates. This construction uses no duality or matrix comparison. -/
def coordinateOriginalNaturalRelationBiproduct :
    (⨁ fun j => ModuleCat.of K (homogeneousSubmodule σ K (b j))) ⟶
      (⨁ fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i))) :=
  (ModuleCat.biproductIsoPi (fun j => ModuleCat.of K (homogeneousSubmodule σ K (b j)))).hom ≫
    ModuleCat.ofHom (coordinateOriginalNaturalRelationMap a b c hc) ≫
      (ModuleCat.biproductIsoPi (fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i)))).inv

/-- The original biproduct map has EXACTLY the original tuple map under
the same mathlib coordinate comparison,not an assumed equality. -/
theorem coordinateOriginalNaturalRelationBiproduct_coordinates :
    LinearStudy.finiteBiproductMapCoordinates
      (fun j => ModuleCat.of K (homogeneousSubmodule σ K (b j)))
      (fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i)))
      (coordinateOriginalNaturalRelationBiproduct a b c hc) =
        coordinateOriginalNaturalRelationMap a b c hc := by
  unfold LinearStudy.finiteBiproductMapCoordinates coordinateOriginalNaturalRelationBiproduct
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.id_comp,
    Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.comp_id]
  rfl

/-- Every ACTUAL original relation component is its ORIGINAL graded
polynomial multiplication entry p_ij=c(e_i)_j. Its degree and negative
zero branch come from ORIGINAL homogeneity hc,not a supplied entry square. -/
theorem coordinateOriginalNaturalRelationBiproduct_component (i : I) (j : J) :
    biproduct.components (coordinateOriginalNaturalRelationBiproduct a b c hc) j i =
      projectiveHomogeneousGradedPolynomialMultiplyEntry (a i) (b j)
        (coordinatePresentationPolynomialEntry a b c hc i j) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  have hv : ((biproduct.components (coordinateOriginalNaturalRelationBiproduct a b c hc) j i) q).1 =
      LinearStudy.integerShiftedFreeMapEntry c i j * q.1 := by
    rw [← LinearStudy.finiteBiproductMapCoordinates_single,
      coordinateOriginalNaturalRelationBiproduct_coordinates]
    exact LinearStudy.integerShiftedFreeNaturalDualRelationMatrix_single
      (homogeneousSubmodule σ K) (Fintype.card σ) a b c hc j i q
  rw [hv]
  by_cases h : b j ≤ a i
  · exact (projectiveHomogeneousGradedPolynomialMultiplyEntry_coe
      (a i) (b j) (coordinatePresentationPolynomialEntry a b c hc i j) q h).symm
  · have hw : coordinatePresentationWeight (σ := σ) (a i) <
        coordinatePresentationWeight (σ := σ) (b j) := by
      unfold coordinatePresentationWeight
      omega
    have hz := LinearStudy.integerShiftedFreeMapEntry_eq_zero (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i))
      (fun j => coordinatePresentationWeight (σ := σ) (b j)) c hc i j hw
    rw [projectiveHomogeneousGradedPolynomialMultiplyEntry_of_lt _ _ _ (Nat.lt_of_not_ge h),hz]
    simp

/-- The matrix of ORIGINAL polynomial transpose entries extracted from
c is the ACTUAL dual of the ORIGINAL relation map in original natural
coordinates. Both the component identity and finite dual assembly are
proved;no dual matrix identity is a hypothesis. -/
theorem coordinateOriginalNaturalRelationBiproduct_dual_matrix :
    projectiveHomogeneousGradedPolynomialDualMatrix a b
        (coordinatePresentationPolynomialEntry a b c hc) ≫
      (LinearStudy.finiteBiproductDualIso
        (fun j => ModuleCat.of K (homogeneousSubmodule σ K (b j)))).hom =
    (LinearStudy.finiteBiproductDualIso
      (fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i)))).hom ≫
        ModuleCat.ofHom (coordinateOriginalNaturalRelationMap a b c hc).dualMap := by
  have h := LinearStudy.finiteBiproductActualMap_dual_matrix
    (fun j => ModuleCat.of K (homogeneousSubmodule σ K (b j)))
    (fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i)))
    (coordinateOriginalNaturalRelationBiproduct a b c hc)
  rw [coordinateOriginalNaturalRelationBiproduct_coordinates] at h
  have he : (fun i j => ModuleCat.ofHom
      (biproduct.components (coordinateOriginalNaturalRelationBiproduct a b c hc) j i).hom.dualMap) =
      (fun i j => projectiveHomogeneousGradedPolynomialDualEntry (a i) (b j)
        (coordinatePresentationPolynomialEntry a b c hc i j)) := by
    funext i j
    rw [coordinateOriginalNaturalRelationBiproduct_component]
    exact projectiveHomogeneousGradedPolynomialMultiplyEntry_dual _ _ _
  rw [he] at h
  exact h

end MvPolynomial
