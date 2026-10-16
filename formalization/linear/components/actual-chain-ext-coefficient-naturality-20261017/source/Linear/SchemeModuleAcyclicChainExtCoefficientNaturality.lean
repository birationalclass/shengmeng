module
public import Linear.SchemeModuleAcyclicChainExtIndependence
public import Linear.SchemeModuleIteratedShiftCoefficientNaturality
public import Linear.SchemeModuleOpcycleHomCoefficientNaturality
public import Linear.SchemeModuleTopHomologyCoefficientNaturality
public import Linear.SchemeModuleAcyclicChainTopExtCoefficientNaturality
public import Linear.SchemeModuleExtSourceIsoCoefficientNaturality
public import Linear.SchemeModuleAcyclicCokernelTopExtCoefficientNaturality
public import Linear.SchemeModuleAcyclicCokernelRankExtCoefficientNaturality
public import Linear.SchemeModuleAcyclicRankCanonicalExtCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL coefficient NatIso for SAME augmented acyclic finite source chain.
The components are EXACTLY the earlier normalized comparison; no replacement is chosen.
This does not identify the original manuscript epsilon class or proper duality. -/
def schemeModuleAcyclicCokernelRankInternalExtNatIso
    (K : ChainComplex X.Modules ℕ) (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e)) (r : ℕ) (hr : 0<r)
    (hAll : ∀ N,schemeModuleChainSourceExtAcyclic K N) (hAbove : IsZero (K.X (r+1))) :
    schemeModuleInternalExtFunctor E r ≅ schemeModuleSourceHomCohomologyFunctor K r :=
  NatIso.ofComponents
    (fun N => schemeModuleAcyclicCokernelRankCanonicalExtIso K E e he N r hr (hAll N) hAbove)
    (by
      intro N M c
      erw [schemeModuleSourceHomCohomologyFunctor_map]
      exact schemeModuleAcyclicCokernelRankCanonicalExtIso_coefficientNaturality
        K E e he c r hr (hAll N) (hAll M) hAbove)

end LinearStudy
