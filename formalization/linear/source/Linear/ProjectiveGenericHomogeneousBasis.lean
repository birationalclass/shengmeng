module
public import Linear.GradedGenericHomogeneousBasis
public import Linear.ProjectiveHomogeneousModuleGenerators
public import Linear.GenericFreeAway
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- A generic basis for the ORIGINAL cone pullback is constructed from actual
homogeneous elements. Its size is the rank of that pullback module, not an
assumed degree formula. The scalar action is explicitly the original map. -/
theorem projectiveCoordinateDomainMap_exists_generic_homogeneous_basis
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let F := FractionRing A
    letI : Algebra A F := inferInstance
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    let N := F ⊗[A] A
    let l : A →ₗ[A] N := TensorProduct.mk A F A 1
    ∃ (m : ℕ) (b : Fin m → A), m = Module.finrank A A ∧
      (∀ i, ∃ d : ℕ, b i ∈ homogeneousQuotientPiece V.ideal.toIdeal d) ∧
      LinearIndependent F (fun i => l (b i)) ∧
      Submodule.span F (Set.range (fun i => l (b i))) = ⊤ := by
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
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let N := F ⊗[A] A
  let l : A →ₗ[A] N := TensorProduct.mk A F A 1
  obtain ⟨m, b, hm, hhom, hli, hspan⟩ :=
    finiteModule_exists_generic_homogeneous_basis
      (A := A) (homogeneousQuotientPiece V.ideal.toIdeal) F l
  have hd : Module.finrank F N = Module.finrank A A :=
    (IsLocalization.finrank_eq F (nonZeroDivisors A) le_rfl).trans
      (IsLocalizedModule.finrank_eq (nonZeroDivisors A) l le_rfl)
  exact ⟨m, b, hm.trans hd, hhom, hli, hspan⟩

end LinearStudy
