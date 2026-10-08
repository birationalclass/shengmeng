/-
Adapted quotient-integrality construction from mathlib NoetherNormalization.
Copyright (c) 2025 Sihan Su. Apache 2.0.
Original authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su.
The coordinate changes here are degree-one shears, not Nagata powers.
-/
module
public import Linear.HomogeneousLinearMonic
public import Linear.PolynomialLinearHighestComponents
public import Mathlib.RingTheory.NoetherNormalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

def polynomialLinearEliminationBaseHom
    (E : MvPolynomial (Fin (n+1)) K ≃ₐ[K] MvPolynomial (Fin (n+1)) K)
    (I : Ideal (MvPolynomial (Fin (n+1)) K)) :
    MvPolynomial (Fin n) K →ₐ[MvPolynomial (Fin n) K]
      Polynomial (MvPolynomial (Fin n) K) ⧸
        (I.map E.toRingHom).map (MvPolynomial.finSuccEquiv K n).toRingHom :=
  (Ideal.Quotient.mkₐ (MvPolynomial (Fin n) K)
      ((I.map E.toRingHom).map (MvPolynomial.finSuccEquiv K n).toRingHom)).comp
    (Algebra.ofId (MvPolynomial (Fin n) K) (Polynomial (MvPolynomial (Fin n) K)))

def polynomialLinearEliminationHom
    (E : MvPolynomial (Fin (n+1)) K ≃ₐ[K] MvPolynomial (Fin (n+1)) K)
    (I : Ideal (MvPolynomial (Fin (n+1)) K)) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n+1)) K ⧸ I :=
  (Ideal.quotientEquivAlg I (I.map E.toRingHom) E rfl).symm.toAlgHom.comp
    ((Ideal.quotientEquivAlg (I.map E.toRingHom)
      ((I.map E.toRingHom).map (MvPolynomial.finSuccEquiv K n).toRingHom)
      (MvPolynomial.finSuccEquiv K n) rfl).symm.toAlgHom.comp
        ((polynomialLinearEliminationBaseHom E I).restrictScalars K))

/-- A real monic equation in the transformed original ideal makes the
actual deletion homomorphism integral. No finite map is postulated. -/
theorem polynomialLinearEliminationHom_isIntegral
    (E : MvPolynomial (Fin (n+1)) K ≃ₐ[K] MvPolynomial (Fin (n+1)) K)
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (H : MvPolynomial (Fin (n+1)) K) (hH : H ∈ I)
    (hu : IsUnit (MvPolynomial.finSuccEquiv K n (E H)).leadingCoeff) :
    (polynomialLinearEliminationHom E I).IsIntegral := by
  have hb : (polynomialLinearEliminationBaseHom E I).IsIntegral := by
    exact (Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu).quotient_isIntegral
      (Submodule.smul_of_tower_mem _ hu.unit⁻¹.val
        (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hH)))
  let e1 : (MvPolynomial (Fin (n+1)) K ⧸ I.map E.toRingHom) ≃ₐ[K]
      (Polynomial (MvPolynomial (Fin n) K) ⧸
        (I.map E.toRingHom).map (MvPolynomial.finSuccEquiv K n).toRingHom) :=
    Ideal.quotientEquivAlg (I.map E.toRingHom)
    ((I.map E.toRingHom).map (MvPolynomial.finSuccEquiv K n).toRingHom)
    (MvPolynomial.finSuccEquiv K n) rfl
  let e2 : (MvPolynomial (Fin (n+1)) K ⧸ I) ≃ₐ[K]
      (MvPolynomial (Fin (n+1)) K ⧸ I.map E.toRingHom) :=
    Ideal.quotientEquivAlg I (I.map E.toRingHom) E rfl
  have he1 : RingHom.IsIntegral
      (R := Polynomial (MvPolynomial (Fin n) K) ⧸
        (I.map E.toRingHom).map (MvPolynomial.finSuccEquiv K n).toRingHom)
      (A := MvPolynomial (Fin (n+1)) K ⧸ I.map E.toRingHom) e1.symm.toRingHom := by
    apply RingHom.isIntegral_of_surjective
    exact e1.symm.surjective
  have he2 : RingHom.IsIntegral
      (R := MvPolynomial (Fin (n+1)) K ⧸ I.map E.toRingHom)
      (A := MvPolynomial (Fin (n+1)) K ⧸ I) e2.symm.toRingHom := by
    apply RingHom.isIntegral_of_surjective
    exact e2.symm.surjective
  change (e2.symm.toRingHom.comp (e1.symm.toRingHom.comp
    (polynomialLinearEliminationBaseHom E I).toRingHom)).IsIntegral
  exact (hb.trans _ _ he1).trans _ _ he2

/-- The map is genuinely induced by the actual linear coordinate forms. -/
theorem polynomialLinearEliminationHom_X
    (E : MvPolynomial (Fin (n+1)) K ≃ₐ[K] MvPolynomial (Fin (n+1)) K)
    (I : Ideal (MvPolynomial (Fin (n+1)) K)) (i : Fin n) :
    polynomialLinearEliminationHom E I (MvPolynomial.X i) =
      Ideal.Quotient.mk I (E.symm (MvPolynomial.X i.succ)) := by
  let J := I.map E.toRingHom
  let J' := J.map (MvPolynomial.finSuccEquiv K n).toRingHom
  let e1 := Ideal.quotientEquivAlg J J' (MvPolynomial.finSuccEquiv K n) rfl
  let e2 := Ideal.quotientEquivAlg I J E rfl
  change e2.symm (e1.symm (Ideal.Quotient.mk J' (Polynomial.C (MvPolynomial.X i)))) = _
  have h1 : Ideal.Quotient.mk J' (Polynomial.C (MvPolynomial.X i)) =
      e1 (Ideal.Quotient.mk J (MvPolynomial.X i.succ)) := by
    change _ = Ideal.Quotient.mk J' (MvPolynomial.finSuccEquiv K n (MvPolynomial.X i.succ))
    rw [MvPolynomial.finSuccEquiv_X_succ]
  rw [h1,e1.symm_apply_apply]
  apply e2.injective
  rw [e2.apply_symm_apply]
  change _ = Ideal.Quotient.mk J (E (E.symm (MvPolynomial.X i.succ)))
  rw [E.apply_symm_apply]

/-- The full polynomial homomorphism, not only generator values, is the
original quotient map applied to the actual inverse coordinate forms. -/
theorem polynomialLinearEliminationHom_formula
    (E : MvPolynomial (Fin (n+1)) K ≃ₐ[K] MvPolynomial (Fin (n+1)) K)
    (I : Ideal (MvPolynomial (Fin (n+1)) K)) (P : MvPolynomial (Fin n) K) :
    polynomialLinearEliminationHom E I P =
      Ideal.Quotient.mk I (E.symm (MvPolynomial.rename Fin.succ P)) := by
  have hh : polynomialLinearEliminationHom E I =
      ((Ideal.Quotient.mkₐ K I).comp E.symm.toAlgHom).comp (MvPolynomial.rename Fin.succ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,Ideal.Quotient.mkₐ_eq_mk,MvPolynomial.rename_X] using
      polynomialLinearEliminationHom_X E I i
  exact DFunLike.congr_fun hh P

/-- A nonzero homogeneous original equation constructs a genuinely linear
integral projection step over an infinite field. -/
theorem homogeneous_exists_linear_integral_elimination [Infinite K]
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (H : MvPolynomial (Fin (n+1)) K) {d : ℕ}
    (hH : H.IsHomogeneous d) (hne : H ≠ 0) (hmem : H ∈ I) :
    ∃ a : Fin n → K, (polynomialLinearEliminationHom (homogeneousCoordinateShearEquiv a) I).IsIntegral ∧
      ∀ i : Fin n, ∃ L : MvPolynomial (Fin (n+1)) K,
        L.IsHomogeneous 1 ∧
          polynomialLinearEliminationHom (homogeneousCoordinateShearEquiv a) I (MvPolynomial.X i) =
            Ideal.Quotient.mk I L := by
  obtain ⟨a,ha⟩ := homogeneous_exists_linear_unit_leadingCoeff H hH hne
  refine ⟨a,polynomialLinearEliminationHom_isIntegral _ I H hmem ha,?_⟩
  intro i
  refine ⟨(homogeneousCoordinateShearEquiv a).symm (MvPolynomial.X i.succ),?_,
    polynomialLinearEliminationHom_X _ I i⟩
  exact homogeneousCoordinateShear_isHomogeneous (-a) _ (MvPolynomial.isHomogeneous_X _ _)

end LinearStudy
