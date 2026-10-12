module
public import Linear.OriginalProjectivePolynomialSection
public import Linear.SheafEmbeddingSectionTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL nonzero-polynomial step at the end of Lemma4.2.
Let j be a sheaf embedding into the ORIGINAL degree-m positive twist,
a a nonzero ACTUAL global section, and Q an ORIGINAL homogeneous polynomial
whose actual restriction equals j(a). Then Q is not in V's ORIGINAL ideal.

The lifting equality and the embedding are explicit: their existence is
NOT asserted here. Canonical identification, Koszul/proper duality and the
eventual Serre lifting remain separate OPEN obligations. -/
theorem originalProjectivePolynomial_lift_after_mono_not_mem {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℕ) (Q : CoordinateRing n)
    (hQ : Q.IsHomogeneous m) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    let T := nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)
    ∀ (F : (Proj 𝓑).Modules) (j : F ⟶ T), Mono j →
      ∀ (a : Γ(F, ⊤)), a ≠ 0 →
        originalProjectivePolynomialSection V m Q hQ = j.app ⊤ a →
        Q ∉ V.ideal.toIdeal := by
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let T := nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
    (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)
  change ∀ (F : (Proj 𝓑).Modules) (j : F ⟶ T), Mono j →
    ∀ (a : Γ(F, ⊤)), a ≠ 0 →
      originalProjectivePolynomialSection V m Q hQ = j.app ⊤ a →
      Q ∉ V.ideal.toIdeal
  intro F j hj a ha hLift
  letI : Mono j := hj
  apply originalProjectivePolynomialSection_nonzero_not_mem V m Q hQ
  rw [hLift]
  exact (moduleSheafMono_section_ne_zero_iff j ⊤ a).mpr ha
end LinearStudy
