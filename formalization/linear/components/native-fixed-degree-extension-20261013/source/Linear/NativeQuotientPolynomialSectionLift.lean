module
public import Linear.NativeHomogeneousQuotientPolynomialLift
public import Linear.NativeHomogeneousGlobalSectionMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL polynomial class Q modulo the ORIGINAL ideal, as an
actual homogeneous section of the associated quotient module on the
ORIGINAL ambient Proj. Its actual localized value is [Q]/1. -/
def ambientHomogeneousQuotientPolynomialSection
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (m : ℕ) (Q : MvPolynomial.homogeneousSubmodule σ K m) :
    letI := homogeneousQuotientGrading I hI
    Γ(nativeProjectiveModuleSheaf (MvPolynomial.homogeneousSubmodule σ K)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I))
      (homogeneousQuotientIntegerDegreeCompatibility I hI) (m : ℤ), ⊤) := by
  letI := homogeneousQuotientGrading I hI
  exact nativeProjectiveModuleHomogeneousGlobalSection (MvPolynomial.homogeneousSubmodule σ K)
    (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I))
    (homogeneousQuotientIntegerDegreeCompatibility I hI) (m : ℤ)
    ⟨Ideal.Quotient.mk I Q,homogeneousQuotientMap_integer_degree I (m : ℤ) Q
      (by simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,ite_true,
        Int.toNat_natCast] using Q.property)⟩

/-- The constructed quotient-polynomial section has the ORIGINAL
localized fraction [Q]/1, with no separate section comparison. -/
theorem ambientHomogeneousQuotientPolynomialSection_apply
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (m : ℕ) (Q : MvPolynomial.homogeneousSubmodule σ K m)
    (p : (⊤ : (Proj (MvPolynomial.homogeneousSubmodule σ K)).Opens)) :
    letI := homogeneousQuotientGrading I hI
    (ambientHomogeneousQuotientPolynomialSection I hI m Q).1 p =
      LocalizedModule.mk (Ideal.Quotient.mk I (Q : MvPolynomial σ K)) 1 := rfl

/-- There is one uniform bound before all degrees and sections such
that EVERY actual ambient quotient-module section is [Q]/1 for an
ORIGINAL homogeneous polynomial Q of its EXACT degree. This closes
the ambient polynomial lifting; transport to the quotient Proj is
explicitly not part of this declaration. -/
theorem homogeneousQuotient_eventually_fraction_polynomial_sections
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (j : σ) :
    letI := homogeneousQuotientGrading I hI
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N → Function.Surjective
      (ambientHomogeneousQuotientPolynomialSection I hI N) := by
  letI := homogeneousQuotientGrading I hI
  obtain ⟨n₀,hn₀⟩ := homogeneousQuotient_eventually_actual_polynomial_lift I hI j
  refine ⟨n₀,fun N hN s => ?_⟩
  obtain ⟨Q,hQ⟩ := hn₀ N hN s
  refine ⟨Q,?_⟩
  let B := MvPolynomial.homogeneousSubmodule σ K
  let D := nativeProjectiveRingIntegerPiece B
  let G := nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece I)
  let hD := nativeProjectiveRingIntegerPiece_graded B
  let hG := homogeneousQuotientIntegerDegreeCompatibility I hI
  let b := Algebra.linearMap (MvPolynomial σ K) (MvPolynomial σ K ⧸ I)
  let hh := fun d x hx => homogeneousQuotientMap_integer_degree I d x hx
  let q : D (N : ℤ) := ⟨Q,by
    simpa only [D,nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,ite_true,
      Int.toNat_natCast] using Q.property⟩
  exact (nativeHomogeneousGlobalSection_degreeZeroMap B D G hD hG b hh (N : ℤ) q).symm.trans hQ
end LinearStudy
