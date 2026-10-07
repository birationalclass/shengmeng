module
public import Linear.ProjectiveAffinePrime
public import Mathlib.RingTheory.Ideal.Maps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem affineChartPolynomialMap_pointKernel_comap (x : Fin n → K) :
    (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).comap
      affineChartPolynomialMap.toRingHom =
        RingHom.ker (MvPolynomial.aeval (R := K) (Fin.cases 1 x)).toRingHom := by
  rw [RingHom.comap_ker]
  exact congrArg (fun φ : (MvPolynomial (Fin (n + 1)) K) →ₐ[K] K => RingHom.ker φ.toRingHom)
    (affineChartPolynomialMap_comp_aeval (K := K) x)

theorem affineChartPolynomialMap_ideal_le_pointKernel
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (x : Fin n → K)
    (hx : Fin.cases 1 x ∈ MvPolynomial.zeroLocus K I) :
    I.map affineChartPolynomialMap.toRingHom ≤
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [affineChartPolynomialMap_pointKernel_comap]
  exact hx

theorem affineChartPolynomialMap_ideal_isPrime_of_point
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    (x : Fin n → K) (hx : Fin.cases 1 x ∈ MvPolynomial.zeroLocus K I) :
    (I.map affineChartPolynomialMap.toRingHom).IsPrime := by
  apply affineChartPolynomialMap_ideal_isPrime I hI
  intro hX
  have h := hx (MvPolynomial.X (0 : Fin (n + 1))) hX
  simpa using h

theorem affineChartPolynomialMap_point_quotient_prime
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (x : Fin n → K)
    (hx : Fin.cases 1 x ∈ MvPolynomial.zeroLocus K I) :
    let J := I.map affineChartPolynomialMap.toRingHom
    let Q := RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
    (Q.map (Ideal.Quotient.mk J)).IsPrime ∧
      (Q.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = Q := by
  intro J Q
  letI : Q.IsPrime := RingHom.ker_isPrime _
  have hJQ : J ≤ Q := affineChartPolynomialMap_ideal_le_pointKernel I x hx
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  refine ⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker, ?_⟩
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change Q ⊔ RingHom.ker (Ideal.Quotient.mk J) = Q
  rw [Ideal.mk_ker, sup_eq_left.mpr hJQ]

end LinearStudy
