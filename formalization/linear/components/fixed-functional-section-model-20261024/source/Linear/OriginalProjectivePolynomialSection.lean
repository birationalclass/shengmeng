module
public import Linear.NativeHomogeneousGlobalSection
public import Linear.Projective
public import Linear.HomogeneousCoordinateGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The restriction of an ORIGINAL homogeneous polynomial to the actual
positive local-fraction sheaf on the ORIGINAL projective variety.
At every homogeneous prime its value is the actual class Q-bar/1.
This definition does not assume or prove eventual section surjectivity. -/
def originalProjectivePolynomialSection {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℕ) (Q : CoordinateRing n)
    (hQ : Q.IsHomogeneous m) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    Γ(nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ), ⊤) := by
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let b : 𝓑 m := ⟨Ideal.Quotient.mk V.ideal.toIdeal Q,⟨Q,hQ,rfl⟩⟩
  let ell : nativeProjectiveRingIntegerPiece 𝓑 (m : ℤ) := ⟨b,by
    simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
      if_true,Int.toNat_natCast] using b.property⟩
  exact nativeProjectiveModuleHomogeneousGlobalSection 𝓑
    (nativeProjectiveRingIntegerPiece 𝓑)
    (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) ell

/-- Nonzero of the lifted ORIGINAL polynomial section implies that
Q is not in the ORIGINAL defining ideal of V. This proves exactly the
nonzero-restriction conclusion, without adding smooth/normal/CM inputs. -/
theorem originalProjectivePolynomialSection_nonzero_not_mem {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℕ) (Q : CoordinateRing n)
    (hQ : Q.IsHomogeneous m) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    originalProjectivePolynomialSection V m Q hQ ≠ 0 → Q ∉ V.ideal.toIdeal := by
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let b : 𝓑 m := ⟨Ideal.Quotient.mk V.ideal.toIdeal Q,⟨Q,hQ,rfl⟩⟩
  let ell : nativeProjectiveRingIntegerPiece 𝓑 (m : ℤ) := ⟨b,by
    simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
      if_true,Int.toNat_natCast] using b.property⟩
  intro hs hmem
  have hell : (ell : CoordinateRing n ⧸ V.ideal.toIdeal) ≠ 0 :=
    nativeProjectiveModuleHomogeneousGlobalSection_element_ne_zero 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) ell hs
  exact hell (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
end LinearStudy
