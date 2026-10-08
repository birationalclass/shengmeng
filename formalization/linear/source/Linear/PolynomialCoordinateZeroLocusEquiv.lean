module
public import Linear.PolynomialReducedPointCount
public import Linear.PolynomialCoordinatePoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K σ τ : Type*} [Field K]

/-- Scalar-valued points transported through an actual quotient algebra
equivalence. No finiteness or reducedness hypothesis. -/
def scalarPointPrecompositionEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) : (A →ₐ[K] K) ≃ (B →ₐ[K] K) where
  toFun φ := φ.comp e.symm.toAlgHom
  invFun ψ := ψ.comp e.toAlgHom
  left_inv φ := by
    ext a
    change φ (e.symm (e a)) = φ a
    rw [e.symm_apply_apply]
  right_inv ψ := by
    ext b
    change ψ (e (e.symm b)) = ψ b
    rw [e.apply_symm_apply]

def polynomialCoordinateZeroLocusEquiv
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ K))
    (hJ : J = I.map E.toRingHom) :
    MvPolynomial.zeroLocus K I ≃ MvPolynomial.zeroLocus K J :=
  (polynomialZeroLocusPointEquiv I).trans
    ((scalarPointPrecompositionEquiv (Ideal.quotientEquivAlg I J E hJ)).trans
      (polynomialZeroLocusPointEquiv J).symm)

/-- The actual polynomial evaluation comparison on every actual point.
The nilpotents of both equation algebras are retained by quotientEquivAlg. -/
theorem polynomialCoordinateZeroLocusEquiv_evaluation
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ K))
    (hJ : J = I.map E.toRingHom)
    (x : MvPolynomial.zeroLocus K I) (F : MvPolynomial σ K) :
    MvPolynomial.eval (polynomialCoordinateZeroLocusEquiv E I J hJ x).val (E F) =
      MvPolynomial.eval x.val F := by
  let eqv := Ideal.quotientEquivAlg I J E hJ
  let φ := polynomialZeroLocusPointEquiv I x
  have h := AlgHom.congr_fun ((polynomialZeroLocusPointEquiv J).apply_symm_apply
    (φ.comp eqv.symm.toAlgHom)) (Ideal.Quotient.mk J (E F))
  change MvPolynomial.eval (polynomialCoordinateZeroLocusEquiv E I J hJ x).val (E F) =
    φ (eqv.symm (Ideal.Quotient.mk J (E F))) at h
  have hm : eqv.symm (Ideal.Quotient.mk J (E F)) = Ideal.Quotient.mk I F := by
    apply eqv.injective
    rw [eqv.apply_symm_apply]
    rfl
  rw [hm] at h
  exact h

end LinearStudy
