module
public import Linear.MappedChainPresentationData
public import Linear.SchemeModuleMappedCokernelProjectionAdjoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Construct the actual supported global comparison from ACTUAL chart
presentation data and an explicit native restriction-unit iso. Original
applications must derive the unit condition from their original cover. -/
def schemeModuleMappedPresentationDataGlobalIso
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).Additive]
    [(Scheme.Modules.restrictFunctor j).PreservesHomology]
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (cokernel (d.1.d 1 0)))) :
    cokernel (d.1.d 1 0) ≅ (Scheme.Modules.pushforward j).obj d.2.2.2.1.pt :=
  schemeModuleSupportedRestrictionIso j _ _ hu
    (mappedChainPresentationDataIso (Scheme.Modules.restrictFunctor j) d)

/-- The explicit ACTUAL global projection equality. This statement
ALONE is not a proof;the next theorem proves it for the constructed map. -/
def schemeModuleMappedPresentationDataGlobalProjection
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).PreservesZeroMorphisms]
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (E : cokernel (d.1.d 1 0) ≅ (Scheme.Modules.pushforward j).obj d.2.2.2.1.pt) : Prop :=
    cokernel.π (d.1.d 1 0) ≫ E.hom =
      ((Scheme.Modules.restrictAdjunction j).homEquiv (d.1.X 0) d.2.2.2.1.pt)
        (d.2.2.1.hom.f 0 ≫ d.2.2.2.1.π)

/-- PROVE the SAME constructed global map carries the quotient
projection to the native adjoint of the actual original chart quotient.
No desired projection identity is an assumption. -/
theorem schemeModuleMappedPresentationDataGlobalIso_projection
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(Scheme.Modules.restrictFunctor j).Additive]
    [(Scheme.Modules.restrictFunctor j).PreservesHomology]
    (d : mappedChainPresentationData (Scheme.Modules.restrictFunctor j))
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (cokernel (d.1.d 1 0)))) :
    schemeModuleMappedPresentationDataGlobalProjection j d
      (schemeModuleMappedPresentationDataGlobalIso j d hu) :=
  schemeModuleMappedCokernelProjectionAdjoint j d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 hu

/-- Transport only the ACTUAL complex through a proved equality,before
specializing large original objects. The unit condition is not altered. -/
theorem schemeModuleCokernelRestrictionUnit_isIso_of_complex_eq
    {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    (C D : ChainComplex Y.Modules ℕ) (h : C = D)
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (cokernel (D.d 1 0)))) :
    IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (cokernel (C.d 1 0))) := by
  subst h
  exact hu

end LinearStudy
