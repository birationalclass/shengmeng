module
public import Negativity.ReesDirectSumCoordinates

@[expose] public section
namespace Negativity
open Polynomial
open scoped DirectSum
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual map of the degree-n ideal-power coefficients. -/
def actualIdealPowerCoefficientMap (I : Ideal R) (n : ℕ) :
    ↥(I ^ n) →ₗ[R] ↥((I.map (algebraMap R S)) ^ n) where
  toFun r := ⟨algebraMap R S r.1, by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ r.2⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := by
    apply Subtype.ext
    exact (Algebra.linearMap R S).map_smul r a.1

/-- Coordinate form of the actual polynomial Rees base-change map. -/
def actualDirectSumReesCoefficientMap (I : Ideal R) :
    (⨁ n : ℕ, ↥(I ^ n)) →+* (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n)) :=
  ((actualReesDirectSumAlgEquiv (I.map (algebraMap R S))).symm.toRingHom.comp
    (actualReesCoefficientMap (S := S) I).toRingHom).comp
      (actualReesDirectSumAlgEquiv I).toRingHom

@[simp]
theorem actualReesCoefficientMap_monomial (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    actualReesCoefficientMap (S := S) I (actualReesPowerMonomial I n r) =
      actualReesPowerMonomial (I.map (algebraMap R S)) n
        (actualIdealPowerCoefficientMap (S := S) I n r) := by
  apply Subtype.ext
  change (monomial n r.1).map (algebraMap R S) = monomial n (algebraMap R S r.1)
  rw [Polynomial.map_monomial]

@[simp]
theorem actualDirectSumReesCoefficientMap_lof (I : Ideal R) (n : ℕ) (r : ↥(I ^ n)) :
    actualDirectSumReesCoefficientMap (S := S) I
        (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n r) =
      DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) n
        (actualIdealPowerCoefficientMap (S := S) I n r) := by
  change (actualReesDirectSumAlgEquiv (I.map (algebraMap R S))).symm
    (actualReesCoefficientMap (S := S) I
      (actualReesDirectSumAlgEquiv I
        (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) n r))) = _
  rw [actualReesDirectSumAlgEquiv_lof, actualReesCoefficientMap_monomial,
    actualReesDirectSumAlgEquiv_symm_monomial]

/-- Restriction of the direct-sum coefficient algebra action along the genuine
map induced by R → S. The homogeneous action is multiplication of actual
ideal-power coefficients. -/
@[instance_reducible]
def actualDirectSumReesBaseModule (I : Ideal R) :
    Module (⨁ n : ℕ, ↥(I ^ n)) (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n)) :=
  Module.compHom _ (actualDirectSumReesCoefficientMap (S := S) I)

theorem actualDirectSumReesBaseModule_lof_smul (I : Ideal R) (m n : ℕ)
    (r : ↥(I ^ m)) (s : ↥((I.map (algebraMap R S)) ^ n)) :
    letI := actualDirectSumReesBaseModule (S := S) I
    (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) m r) •
        (DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) n s) =
      DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) (m + n)
        (GradedMonoid.GMul.mul
          (A := fun n : ℕ => ↥((I.map (algebraMap R S)) ^ n))
          (actualIdealPowerCoefficientMap (S := S) I m r) s) := by
  letI := actualDirectSumReesBaseModule (S := S) I
  change actualDirectSumReesCoefficientMap (S := S) I
      (DirectSum.lof R ℕ (fun n => ↥(I ^ n)) m r) *
      (DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) n s) = _
  rw [actualDirectSumReesCoefficientMap_lof]
  simp only [DirectSum.lof_eq_of, DirectSum.of_mul_of]

/-- The polynomial Rees action on a chart equals the previously constructed
homogeneous direct-sum ideal-power action, with no flatness assumption. -/
theorem actualPolynomialReesBaseModule_monomial_smul (I : Ideal R) (m n : ℕ)
    (r : ↥(I ^ m)) (s : ↥((I.map (algebraMap R S)) ^ n)) :
    letI := actualDirectSumReesBaseModule (S := S) I
    letI := actualPolynomialReesModule I
      (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n))
    (actualReesPowerMonomial I m r) •
        (DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) n s) =
      DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) (m + n)
        (GradedMonoid.GMul.mul
          (A := fun n : ℕ => ↥((I.map (algebraMap R S)) ^ n))
          (actualIdealPowerCoefficientMap (S := S) I m r) s) := by
  letI := actualDirectSumReesBaseModule (S := S) I
  letI := actualPolynomialReesModule I
    (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n))
  rw [actualPolynomialReesModule_monomial_smul]
  exact actualDirectSumReesBaseModule_lof_smul (S := S) I m n r s

/-- Restriction of scalars through the actual polynomial coefficient map. -/
@[instance_reducible]
def actualPolynomialReesCoefficientModule (I : Ideal R) :
    Module (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) :=
  Module.compHom _ (actualReesCoefficientMap (S := S) I).toRingHom

/-- The polynomial-coordinate isomorphism on an affine chart respects all
base Rees scalars, not only individual homogeneous monomials. -/
def actualReesBaseChangeLinearEquiv (I : Ideal R) :
    letI := actualDirectSumReesBaseModule (S := S) I
    letI := actualPolynomialReesModule I
      (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n))
    letI := actualPolynomialReesCoefficientModule (S := S) I
    (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n)) ≃ₗ[reesAlgebra I]
      reesAlgebra (I.map (algebraMap R S)) := by
  letI := actualDirectSumReesBaseModule (S := S) I
  letI := actualPolynomialReesModule I
    (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n))
  letI := actualPolynomialReesCoefficientModule (S := S) I
  refine { (actualReesDirectSumAlgEquiv (I.map (algebraMap R S))).toEquiv with
    map_add' := (actualReesDirectSumAlgEquiv (I.map (algebraMap R S))).map_add
    map_smul' := ?_ }
  intro p a
  change actualReesDirectSumAlgEquiv (I.map (algebraMap R S))
      (actualDirectSumReesCoefficientMap (S := S) I
        ((actualReesDirectSumAlgEquiv I).symm p) * a) =
    actualReesCoefficientMap (S := S) I p *
      actualReesDirectSumAlgEquiv (I.map (algebraMap R S)) a
  rw [map_mul]
  congr 1
  change actualReesDirectSumAlgEquiv (I.map (algebraMap R S))
      ((actualReesDirectSumAlgEquiv (I.map (algebraMap R S))).symm
        (actualReesCoefficientMap (S := S) I
          (actualReesDirectSumAlgEquiv I ((actualReesDirectSumAlgEquiv I).symm p)))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

@[simp]
theorem actualReesBaseChangeLinearEquiv_lof (I : Ideal R) (n : ℕ)
    (s : ↥((I.map (algebraMap R S)) ^ n)) :
    letI := actualDirectSumReesBaseModule (S := S) I
    letI := actualPolynomialReesModule I
      (⨁ n : ℕ, ↥((I.map (algebraMap R S)) ^ n))
    letI := actualPolynomialReesCoefficientModule (S := S) I
    actualReesBaseChangeLinearEquiv (S := S) I
      (DirectSum.lof S ℕ (fun n => ↥((I.map (algebraMap R S)) ^ n)) n s) =
        actualReesPowerMonomial (I.map (algebraMap R S)) n s :=
  actualReesDirectSumAlgEquiv_lof _ n s

#print axioms actualDirectSumReesCoefficientMap_lof
#print axioms actualPolynomialReesBaseModule_monomial_smul
#print axioms actualReesBaseChangeLinearEquiv
end
end Negativity
