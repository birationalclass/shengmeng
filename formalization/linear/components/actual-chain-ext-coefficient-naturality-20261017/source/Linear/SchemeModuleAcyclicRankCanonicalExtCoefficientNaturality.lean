module
public import Linear.SchemeModuleAcyclicChainExtIndependence
public import Linear.SchemeModuleIteratedShiftCoefficientNaturality
public import Linear.SchemeModuleOpcycleHomCoefficientNaturality
public import Linear.SchemeModuleTopHomologyCoefficientNaturality
public import Linear.SchemeModuleAcyclicChainTopExtCoefficientNaturality
public import Linear.SchemeModuleExtSourceIsoCoefficientNaturality
public import Linear.SchemeModuleAcyclicCokernelTopExtCoefficientNaturality
public import Linear.SchemeModuleAcyclicCokernelRankExtCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Native chosen-resolution comparison satisfies the proved coefficient square. -/
theorem schemeModuleAcyclicCokernelRankCanonicalExtIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    {N M : X.Modules} (c : N ⟶ M) (r : ℕ) (hr : 0<r)
    (hN : schemeModuleChainSourceExtAcyclic K N) (hM : schemeModuleChainSourceExtAcyclic K M)
    (hAbove : IsZero (K.X (r+1))) :
    (schemeModuleInternalExtFunctor E r).map c ≫
        (schemeModuleAcyclicCokernelRankCanonicalExtIso K E e he M r hr hM hAbove).hom =
      (schemeModuleAcyclicCokernelRankCanonicalExtIso K E e he N r hr hN hAbove).hom ≫
        HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) r := by
  let I : InjectiveResolution N := injectiveResolution N
  let J : InjectiveResolution M := injectiveResolution M
  erw [schemeModuleAcyclicCokernelRankCanonicalExtIso_eq_viaResolution K E e he M J r hr hM hAbove,
    schemeModuleAcyclicCokernelRankCanonicalExtIso_eq_viaResolution K E e he N I r hr hN hAbove]
  exact schemeModuleAcyclicCokernelRankInternalExtIso_coefficientNaturality K E e he c I J r hr hN hM hAbove


end LinearStudy
