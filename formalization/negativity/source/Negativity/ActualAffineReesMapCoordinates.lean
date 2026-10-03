module

public import Negativity.ActualRelativeReesScheme
public import Negativity.ReesImageCoordinates
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def actualAffineReesCoordinates (I : Ideal R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (actualReesProjection I)
      ≅ Spec (.of (S ⊗[R] reesAlgebra I)) :=
  pullbackSpecIso R S (reesAlgebra I)

def actualAffinePolynomialCoordinates :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualPolynomialProjection (R := R)) ≅ Spec (.of S[X]) :=
  pullbackSpecIso R S R[X] ≪≫
    Scheme.Spec.mapIso (polyEquivTensor' R S).toRingEquiv.toCommRingCatIso.op

theorem actual_affine_polynomial_coordinates_inv_fst :
    (actualAffinePolynomialCoordinates (R := R) (S := S)).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (C : S →+* S[X])) := by
  simp only [actualAffinePolynomialCoordinates, actualPolynomialProjection, Iso.trans_inv, Category.assoc,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (polyEquivTensor' R S).symm (s ⊗ₜ[R] (1 : R[X])) = C s
  simp only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul,
    Polynomial.map_one]
  simp [Polynomial.smul_eq_C_mul]

theorem actual_affine_polynomial_coordinates_inv_snd :
    (actualAffinePolynomialCoordinates (R := R) (S := S)).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap R S))) := by
  simp only [actualAffinePolynomialCoordinates, actualPolynomialProjection, Iso.trans_inv, Category.assoc,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change (polyEquivTensor' R S).symm ((1 : S) ⊗ₜ[R] p) = p.map (algebraMap R S)
  simp [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul]

set_option maxHeartbeats 800000 in
/-- Final theorem: the actual morphism from polynomial base change to
Rees base change has precisely the tensor-to-polynomial coordinate
map a ⊗ p ↦ a·p. Thus the algebraic image-coordinate calculation
applies to the genuine scheme morphism, without a chart-compatibility
assumption. -/
theorem actual_affine_polynomial_rees_map_coordinates (I : Ideal R) :
    actualPolynomialReesMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) I ≫
        (actualAffineReesCoordinates (S := S) I).hom =
      (actualAffinePolynomialCoordinates (R := R) (S := S)).hom ≫
        Spec.map (CommRingCat.ofHom (actualReesPolynomialMap (S := S) I).toRingHom) := by
  rw [← cancel_epi (actualAffinePolynomialCoordinates (R := R) (S := S)).inv]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  apply pullback.hom_ext
  · simp only [Category.assoc, actualPolynomialReesMap, pullback.map, pullback.lift_fst,
      Category.comp_id, actual_affine_polynomial_coordinates_inv_fst,
      actualAffineReesCoordinates, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    change C s = (actualReesPolynomialMap I) (s ⊗ₜ[R] (1 : reesAlgebra I))
    simp [actualReesPolynomialMap, actualReesBaseChangeMap, actualReesCoefficientMap,
      Polynomial.smul_eq_C_mul]
  · simp only [Category.assoc, actualPolynomialReesMap, pullback.map, pullback.lift_snd,
      actualAffineReesCoordinates, pullbackSpecIso_inv_snd]
    rw [← Category.assoc, actual_affine_polynomial_coordinates_inv_snd]
    simp only [actualPolynomialToRees, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change p.1.map (algebraMap R S) = (actualReesPolynomialMap I) ((1 : S) ⊗ₜ[R] p)
    simp [actualReesPolynomialMap, actualReesBaseChangeMap, actualReesCoefficientMap]

end
end Negativity
