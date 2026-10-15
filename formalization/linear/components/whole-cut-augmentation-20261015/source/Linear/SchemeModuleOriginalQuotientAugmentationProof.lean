module
public import Linear.SchemeModulePresentationTargetAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Transport the proved original projection to a LITERAL chart quotient
before specializing any projective coordinate data. The source equality
is explicit here and proved for the original native presentation below.
The returned term proves existence of an actual chain augmentation and
its zero-component formula; no desired formula is an input. -/
def schemeModuleOriginalQuotientAugmentationProof
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).Additive]
    [(Scheme.Modules.restrictFunctor j).PreservesHomology]
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (M : X.Modules) (hM : d.2.2.2.1.pt = M)
    (h : ∃ E : cokernel (d.1.d 1 0) ≅ (Scheme.Modules.pushforward j).obj d.2.2.2.1.pt,
      schemeModuleMappedPresentationDataGlobalProjection j d E)
    (T : Y.Modules) (rho : (Scheme.Modules.pushforward j).obj M ≅ T) :=
  schemeModuleMappedPresentationDataTargetAugmentation_exists j d T
    ((Scheme.Modules.pushforward j).mapIso (eqToIso hM) ≪≫ rho) h

end LinearStudy
