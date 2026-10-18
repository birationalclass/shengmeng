module
public import Linear.NativeKoszulTargetOffCutZero
public import Linear.ProjectivePulledOriginalNativeCokernelIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms projectivePulledWholeCutResolutionTarget
  projectivePulledOriginalNativeCokernelIso
variable {n r : ℕ}
/-- Actual ORIGINAL target vanishes on each ORIGINAL equation-nonzero
open. Only the already derived source iso is used;no Ext or main-chart
restriction-unit comparison is required. -/
def projectivePulledOriginalTargetOffCutZeroProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) (i : Fin r) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  nativeProjectiveKoszul_target_openRestriction_isZero_offCut
    (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) i k
    (projectivePulledWholeCutResolutionTarget f V L hL w k)
    (projectivePulledOriginalNativeCokernelIso f V L hL w k e)
    (Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (projectivePulledLinearKoszulForms f V L w i)).ι (fun x => x.property)
end LinearStudy
