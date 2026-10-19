module
public import Linear.ProjectivePulledLinearKoszulGlobal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra HasFiniteBiproducts.of_hasFiniteProducts
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
variable {n r : ℕ}
/-- Precompiled actual term identification on SAME original complex.
This is an OBJECT isomorphism,not a Prop proof. Its actual native
exterior basis is the same one as the original global Koszul complex. -/
def projectivePulledOriginalTermTwistIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) (p : ℕ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectivePulledLinearKoszulComplex f V L hL w k).X p ≅
      biproduct (fun _ : Set.powersetCard (Fin r) p =>
        nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
          (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
          (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal))
          (k-(p : ℤ)*(f.degree : ℤ))) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  change (nativeProjectiveKoszulComplex (homogeneousQuotientPiece V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k).X p ≅ _
  rw [nativeProjectiveKoszulComplex_X]
  exact nativeProjectiveKoszulTermTwistIso (homogeneousQuotientPiece V.ideal.toIdeal) r f.degree p k
end LinearStudy
