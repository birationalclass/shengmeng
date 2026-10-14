module
public import Linear.NativeOriginalRelationNaturalComponents
public import Mathlib.Algebra.Category.ModuleCat.Abelian
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

/-- Assemble the ORIGINAL homogeneous polynomial piece duals and the
proved original degree -N coordinate equivalence. This is the original
coefficient comparison,not a separately chosen duality input. -/
def coordinateOriginalDegreeCoefficientDualIso {L : Type} [Fintype L] [DecidableEq L] (a : L → ℕ) :
    (⨁ fun i => ModuleCat.of K (Module.Dual K (homogeneousSubmodule σ K (a i)))) ≅
      ModuleCat.of K (Module.Dual K
        (LinearStudy.integerShiftedFreeDualCoordinatePiece (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)) (-(Fintype.card σ:ℤ)))) :=
  (LinearStudy.finiteBiproductDualIso (fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i)))).trans
    (LinearStudy.integerShiftedFreeDualNaturalCoordinatePiEquiv
      (homogeneousSubmodule σ K) (Fintype.card σ) a).dualMap.toModuleIso

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (a : I → ℕ) (b : J → ℕ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)

/-- The ORIGINAL polynomial dual matrix whose entries are extracted from
c is the ACTUAL dual of ORIGINAL Delta_-N under the constructed ORIGINAL
coefficient dual comparisons. No relation-dual matrix square is assumed. -/
theorem coordinateOriginalDegreeRelationDual_matrix :
    projectiveHomogeneousGradedPolynomialDualMatrix a b
        (coordinatePresentationPolynomialEntry a b c hc) ≫
      (coordinateOriginalDegreeCoefficientDualIso b).hom =
    (coordinateOriginalDegreeCoefficientDualIso a).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c
        (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc
        (-(Fintype.card σ:ℤ))).dualMap := by
  unfold coordinateOriginalDegreeCoefficientDualIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc,coordinateOriginalNaturalRelationBiproduct_dual_matrix,Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun t => (LinearStudy.finiteBiproductDualIso
    (fun i => ModuleCat.of K (homogeneousSubmodule σ K (a i)))).hom ≫ t)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change φ (LinearStudy.integerShiftedFreeDualNaturalCoordinatePiEquiv
      (homogeneousSubmodule σ K) (Fintype.card σ) a
      (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc (-(Fintype.card σ:ℤ))
        ((LinearStudy.integerShiftedFreeDualNaturalCoordinatePiEquiv
          (homogeneousSubmodule σ K) (Fintype.card σ) b).symm
            (LinearStudy.integerShiftedFreeDualNaturalCoordinatePiEquiv
              (homogeneousSubmodule σ K) (Fintype.card σ) b x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The ORIGINAL polynomial matrix cokernel and ORIGINAL degree-relation
dual cokernel are canonically the same. The actual matrix square is proved
from c,its original grading,actual entries and original finite dual assembly. -/
def coordinateOriginalDegreeRelationDualCokernelIso :
    cokernel (projectiveHomogeneousGradedPolynomialDualMatrix a b
      (coordinatePresentationPolynomialEntry a b c hc)) ≅
    cokernel (ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c
      (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i))
      (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc
      (-(Fintype.card σ:ℤ))).dualMap) :=
  cokernel.mapIso _ _ (coordinateOriginalDegreeCoefficientDualIso a)
    (coordinateOriginalDegreeCoefficientDualIso b)
    (coordinateOriginalDegreeRelationDual_matrix a b c hc)

/-- The original degree-relation cokernel alignment preserves the
ORIGINAL polynomial quotient map,with the ORIGINAL coefficient dual map. -/
theorem coordinateOriginalDegreeRelationDualCokernelIso_quotient :
    cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b
        (coordinatePresentationPolynomialEntry a b c hc)) ≫
      (coordinateOriginalDegreeRelationDualCokernelIso a b c hc).hom =
    (coordinateOriginalDegreeCoefficientDualIso b).hom ≫
      cokernel.π (ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualDegreeRelationMatrix c
        (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc
        (-(Fintype.card σ:ℤ))).dualMap) := by
  unfold coordinateOriginalDegreeRelationDualCokernelIso
  erw [cokernel.mapIso_hom]
  simp [cokernel.map]

end MvPolynomial
