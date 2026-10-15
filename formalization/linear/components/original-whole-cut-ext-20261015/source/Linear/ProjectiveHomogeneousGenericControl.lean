module
public import Linear.ProjectiveGenericHomogeneousBasis
public import Linear.GenericSpanDenominator
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- For the ORIGINAL pullback, construct a homogeneous independent family
of the actual generic rank and ONE nonzero denominator that controls every
coordinate function. No basis or denominator is an extra hypothesis. -/
theorem projectiveCoordinateDomainMap_exists_homogeneous_generic_control
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    ∃ (m : ℕ) (b : Fin m → A) (r : A),
      m = Module.finrank A A ∧
      (∀ i, ∃ d : ℕ, b i ∈ homogeneousQuotientPiece V.ideal.toIdeal d) ∧
      LinearIndependent A b ∧ r ≠ 0 ∧
      ∀ x : A, ∃ c : Fin m → A, (∑ i, φ (c i) * b i) = φ r * x := by
  classical
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let F := FractionRing A
  letI : Algebra A F := inferInstance
  letI : IsFractionRing A F := inferInstance
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  letI : Algebra A A := φ.toRingHom.toAlgebra
  letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
  letI : Module A A := Algebra.toModule
  letI : Module.Finite A A := projectiveCoordinateDomainMap_finite f V hq hf hV
  let N := F ⊗[A] A
  let l : A →ₗ[A] N := TensorProduct.mk A F A 1
  obtain ⟨m, b, hm, hhom, hli, hspan⟩ :=
    projectiveCoordinateDomainMap_exists_generic_homogeneous_basis f V hq hf hV
  have hliA : LinearIndependent A (fun i => l (b i)) := hli.restrict_scalars' A
  have hb : LinearIndependent A b := hliA.of_comp l
  obtain ⟨r, hr, hden⟩ := finiteModule_genericFamily_exists_common_denominator F l b hspan
  refine ⟨m, b, r, hm, hhom, hb, hr, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hden x)
  refine ⟨c, ?_⟩
  change (∑ i, φ (c i) * b i) = φ r * x at hc
  exact hc

end LinearStudy
