module
public import Linear.PolynomialProjectionFiberQuotient
public import Linear.PolynomialReducedPointCount
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace LinearStudy

/-- For the actual finite dominant polynomial projection, its original
equation fiber quotient is finite and reduced on a derived nonempty open.
The ideal, not only its zero-point set, is proved radical. -/
theorem polynomial_finite_projection_exists_radical_equation_fibers
    {K σ τ : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (L : τ → MvPolynomial σ K)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)))
    (hfinite : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)).Finite) :
    let R := MvPolynomial τ K
    let A := MvPolynomial σ K ⧸ I
    let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
    letI : Module R A := Algebra.toModule
    ∃ c : R,c ≠ 0 ∧ ∀ w : τ → K,MvPolynomial.eval w c ≠ 0 →
      let J := polynomialProjectionFiberIdeal I L w
      J.IsRadical ∧ Module.Finite K (MvPolynomial σ K ⧸ J) ∧
        Module.finrank K (MvPolynomial σ K ⧸ J)=Module.finrank R A ∧
        Nat.card (MvPolynomial.zeroLocus K J)=Module.finrank R A := by
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  letI : Algebra.FinitePresentation K R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c,hc,hfib⟩ := finite_injective_algHom_exists_reduced_rank_fibers φ hinj hfinite
  refine ⟨c,hc,?_⟩
  intro w hw
  let ρ : R →ₐ[K] K := MvPolynomial.aeval w
  letI : Algebra R K := ρ.toRingHom.toAlgebra
  letI : SMul R K := ρ.toRingHom.toAlgebra.toSMul
  letI : Module R K := Algebra.toModule
  letI : IsScalarTower K R A := IsScalarTower.of_algHom φ
  letI : IsScalarTower K R K := IsScalarTower.of_algHom ρ
  obtain ⟨hfiniteT,hredT,hrank,_⟩ := hfib ρ hw
  letI := hfiniteT
  letI := hredT
  let J := polynomialProjectionFiberIdeal I L w
  let Q := MvPolynomial σ K ⧸ J
  obtain ⟨E⟩ := polynomialProjectionFiber_exists_tensor_equiv I L w
  let e : Q ≃ₗ[K] K ⊗[R] A := E.symm.toLinearEquiv.trans
    ((TensorProduct.comm R A K).restrictScalars K)
  letI : Module.Finite K Q := Module.Finite.equiv e.symm
  let Ecomm := Algebra.TensorProduct.comm R A K
  letI : IsReduced Q := isReduced_of_injective (Ecomm.toRingHom.comp E.symm.toRingHom)
    (Ecomm.injective.comp E.symm.injective)
  have hd : Module.finrank K Q=Module.finrank R A := e.finrank_eq.trans hrank
  exact ⟨(Ideal.isRadical_iff_quotient_reduced J).mpr inferInstance,inferInstance,hd,
    (polynomialZeroLocus_card_eq_finrank J).trans hd⟩

end LinearStudy
