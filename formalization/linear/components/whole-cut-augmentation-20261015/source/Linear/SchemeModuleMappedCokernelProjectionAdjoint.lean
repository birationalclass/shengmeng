module
public import Linear.SchemeModuleSupportedProjectionAdjoint
public import Linear.MappedChainCokernelPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- For ACTUAL original module complexes,the native global supported
cokernel comparison carries the SAME original quotient projection to
the native ADJOINT of the SAME original affine cofork projection.
Source complex/chart iso and cofork colimit are explicit generic inputs;
original Koszul applications already construct all of them. -/
theorem schemeModuleMappedCokernelProjectionAdjoint
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).Additive]
    [(Scheme.Modules.restrictFunctor j).PreservesHomology]
    (C : ChainComplex Y.Modules ℕ) (D : ChainComplex X.Modules ℕ)
    (e : (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q)
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (cokernel (C.d 1 0)))) :
    cokernel.π (C.d 1 0) ≫
      (schemeModuleSupportedRestrictionIso j (cokernel (C.d 1 0)) Q.pt hu
        (mappedChainFirstCokernelPresentationIso (Scheme.Modules.restrictFunctor j) C D e Q hQ)).hom =
      ((Scheme.Modules.restrictAdjunction j).homEquiv (C.X 0) Q.pt) (e.hom.f 0 ≫ Q.π) := by
  apply schemeModuleSupportedRestrictionIso_projection_adjoint
  exact mappedChainFirstCokernelPresentationIso_projection (Scheme.Modules.restrictFunctor j) C D e Q hQ

end LinearStudy