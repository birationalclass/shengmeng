module
public import Linear.NativeProjectiveKoszulTopModuleFrame
public import Linear.ProjectivePulledOriginalChartPresentation
public import Linear.ProjectivePulledWholeCutResolutionObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] nativeProjectiveKoszulTopChartModuleFrameLaw homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
  CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- Construct the ACTUAL original top coefficient frame through the
smaller native graded-chart boundary. Not an assumed trivialization. -/
def projectivePulledOriginalTopChartModuleFrame
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  nativeProjectiveKoszulTopChartModuleFrame (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩

/-- Explicit STATEMENT for the SAME original maps,in their constructed
induced frame. Independent conventional-frame compatibility is separate. -/
def projectivePulledOriginalTopChartModuleFrameLaw
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  nativeProjectiveKoszulTopChartModuleFrameLaw (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩

/-- Prove actual original top-functional normalization to MODULE identity.
This does not assert internal SHEAF Ext/support or completed original4.2. -/
theorem projectivePulledOriginalTopChartModuleFrameLaw_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    projectivePulledOriginalTopChartModuleFrameLaw f V L hL w k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact nativeProjectiveKoszulTopChartModuleFrameLaw_proof (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩

end LinearStudy
