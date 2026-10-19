module
public import Linear.FiniteLinearProjectionGoodOpen
public import Linear.GenericFiberRankOpen
public import Linear.UnramifiedEvaluationQuotient
public import Linear.FiniteReducedAlgebraPoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace LinearStudy

/-- The actual base-changed fiber over a scalar evaluation is reduced
when its whole inverse image belongs to the constructed unramified open. -/
theorem finite_projection_tensor_fiber_isReduced
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A]
    (φ : R →ₐ[K] A) (ρ : R →ₐ[K] K) (hfinite : φ.Finite)
    (c : R) (hc : ρ c ≠ 0)
    (hgood : letI : Algebra R A := φ.toRingHom.toAlgebra
      ↑(PrimeSpectrum.basicOpen (φ c)) ⊆ Algebra.unramifiedLocus R A) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : Algebra R K := ρ.toRingHom.toAlgebra
    IsReduced (K ⊗[R] A) := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Algebra R K := ρ.toRingHom.toAlgebra
  letI : Module.Finite R A := hfinite
  let T := K ⊗[R] A
  let ψ : A →+* T := (Algebra.TensorProduct.includeRight : A →ₐ[R] T).toRingHom
  have hρ : Function.Surjective (algebraMap R K) := by
    intro k
    exact ⟨algebraMap K R k,ρ.commutes k⟩
  have hψ : Function.Surjective ψ := Algebra.TensorProduct.includeRight_surjective A hρ
  have he : ψ.comp φ.toRingHom = (algebraMap K T).comp ρ.toRingHom := by
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := K) (B := A)).symm
  exact isReduced_of_unramified_evaluation_quotient φ.toRingHom ρ.toRingHom ψ c
    hψ he hc hgood

/-- A finite dominant projection has actual finite reduced generic
fibers whose number of scalar-valued points equals its generic rank.
This does NOT yet identify that rank with projective degree V. -/
theorem finite_injective_algHom_exists_reduced_rank_fibers
    {K R A : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R] [Algebra.FinitePresentation K R]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FinitePresentation K A]
    (φ : R →ₐ[K] A) (hinj : Function.Injective φ) (hfinite : φ.Finite) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    ∃ c : R, c ≠ 0 ∧ ∀ ρ : R →ₐ[K] K, ρ c ≠ 0 →
      letI : Algebra R K := ρ.toRingHom.toAlgebra
      Module.Finite K (K ⊗[R] A) ∧ IsReduced (K ⊗[R] A) ∧
        Module.finrank K (K ⊗[R] A) = Module.finrank R A ∧
        Nat.card ((K ⊗[R] A) →ₐ[K] K) = Module.finrank R A := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Module.Finite R A := hfinite
  obtain ⟨a,ha,_,hgood⟩ := finite_injective_algHom_exists_target_good_loci φ hinj hfinite
  obtain ⟨b,hb,hrank⟩ := finiteModule_exists_fiber_rank_open (R := R) (M := A) (K := K)
  refine ⟨a*b,mul_ne_zero ha hb,?_⟩
  intro ρ hc
  letI : Algebra R K := ρ.toRingHom.toAlgebra
  have hca : ρ a ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [map_mul] using hc)).1
  have hcb : ρ b ≠ 0 := (mul_ne_zero_iff.mp (by simpa only [map_mul] using hc)).2
  have hgood' : ↑(PrimeSpectrum.basicOpen (φ a)) ⊆ Algebra.unramifiedLocus R A := by
    intro P hP
    exact (hgood P hP).2.2
  letI : IsReduced (K ⊗[R] A) := finite_projection_tensor_fiber_isReduced φ ρ hfinite a hca hgood'
  have hdim := hrank ρ.toRingHom hcb
  refine ⟨inferInstance,inferInstance,hdim,?_⟩
  exact (finiteReducedAlgebra_finrank_eq_rationalPoint_card (K := K) (A := K ⊗[R] A)).symm.trans hdim

end LinearStudy
