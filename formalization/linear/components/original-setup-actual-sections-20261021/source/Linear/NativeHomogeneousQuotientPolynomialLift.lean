module
public import Linear.NativeFiniteGradedPolynomialLift
public import Linear.HomogeneousCoordinateGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual original quotient map preserves its actual integer
homogeneous pieces, including all negative degrees. -/
theorem homogeneousQuotientMap_integer_degree
    (I : Ideal (MvPolynomial σ K)) (d : ℤ) (x : MvPolynomial σ K)
    (hx : x ∈ nativeProjectiveRingIntegerPiece (MvPolynomial.homogeneousSubmodule σ K) d) :
    Ideal.Quotient.mk I x ∈ nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I) d := by
  unfold nativeProjectiveRingIntegerPiece at hx ⊢
  by_cases hd : 0 ≤ d
  · rw [ite_eq_left hd] at hx ⊢
    exact (homogeneousQuotientPiece_mem_iff I d.toNat _).mpr ⟨x,hx,rfl⟩
  · rw [ite_eq_right hd,Submodule.mem_bot] at hx ⊢
    rw [hx,map_zero]

/-- The quotient's scalar grading is derived from the SAME polynomial
quotient map; it is not supplied as another input. -/
theorem homogeneousQuotientIntegerDegreeCompatibility
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    letI := homogeneousQuotientGrading I hI
    ∀ a : ℕ, ∀ d : ℤ, ∀ c : MvPolynomial σ K,
      c ∈ MvPolynomial.homogeneousSubmodule σ K a →
      ∀ x : MvPolynomial σ K ⧸ I,
        x ∈ nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I) d →
        c • x ∈ nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I) ((a : ℤ)+d) := by
  letI := homogeneousQuotientGrading I hI
  intro a d c hc x hx
  have hclass : Ideal.Quotient.mk I c ∈ homogeneousQuotientPiece I a :=
    (homogeneousQuotientPiece_mem_iff I a _).mpr ⟨c,hc,rfl⟩
  change Ideal.Quotient.mk I c * x ∈ _
  exact nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece I)
    a d (Ideal.Quotient.mk I c) hclass x hx

/-- For ANY actual homogeneous polynomial ideal, there is one uniform
bound before all later degrees such that every actual section of the
associated quotient module on the ORIGINAL ambient Proj is the actual
image of an original degree-N homogeneous polynomial. No prime, smooth,
normal or Cohen--Macaulay assumption is imposed. Identification with
the quotient Proj's own structure twist remains a separate obligation. -/
theorem homogeneousQuotient_eventually_actual_polynomial_lift
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (j : σ) :
    letI := homogeneousQuotientGrading I hI
    let G := nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I)
    let hG := homogeneousQuotientIntegerDegreeCompatibility I hI
    let b := Algebra.linearMap (MvPolynomial σ K) (MvPolynomial σ K ⧸ I)
    let hh := fun d x hx => homogeneousQuotientMap_integer_degree I d x hx
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∀ s : Γ(nativeProjectiveModuleSheaf (MvPolynomial.homogeneousSubmodule σ K) G hG
        (N : ℤ), ⊤),
      ∃ Q : MvPolynomial.homogeneousSubmodule σ K N,
        ((nativeProjectiveDegreeZeroSheafMap (MvPolynomial.homogeneousSubmodule σ K)
          (nativeProjectiveRingIntegerPiece (MvPolynomial.homogeneousSubmodule σ K)) G
          (nativeProjectiveRingIntegerPiece_graded (MvPolynomial.homogeneousSubmodule σ K))
          hG b hh (N : ℤ)).app ⊤)
          (nativePositiveHomogeneousGlobalSection (MvPolynomial.homogeneousSubmodule σ K) N Q) = s := by
  letI := homogeneousQuotientGrading I hI
  let G := nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I)
  letI : DirectSum.Decomposition G := nativeProjectiveRingIntegerDecomposition (homogeneousQuotientPiece I)
  exact MvPolynomial.coordinateNativeGradedQuotient_eventually_polynomial_lift G
    (homogeneousQuotientIntegerDegreeCompatibility I hI)
    (Algebra.linearMap (MvPolynomial σ K) (MvPolynomial σ K ⧸ I))
    (fun d x hx => homogeneousQuotientMap_integer_degree I d x hx)
    (Ideal.Quotient.mk_surjective) j
end LinearStudy
