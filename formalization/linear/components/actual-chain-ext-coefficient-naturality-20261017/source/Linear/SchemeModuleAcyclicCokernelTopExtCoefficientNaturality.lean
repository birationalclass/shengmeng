module
public import Linear.SchemeModuleAcyclicChainExtIndependence
public import Linear.SchemeModuleIteratedShiftCoefficientNaturality
public import Linear.SchemeModuleOpcycleHomCoefficientNaturality
public import Linear.SchemeModuleTopHomologyCoefficientNaturality
public import Linear.SchemeModuleAcyclicChainTopExtCoefficientNaturality
public import Linear.SchemeModuleExtSourceIsoCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Keep SAME actual cokernel target and SAME augmentation while varying coefficients. -/
theorem schemeModuleAcyclicCokernelTopInternalExtIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    {N M : X.Modules} (c : N ⟶ M) (I : InjectiveResolution N) (J : InjectiveResolution M)
    (q : ℕ) (hN : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hM : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) M (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    (schemeModuleInternalExtFunctor E (q+1)).map c ≫
        (schemeModuleAcyclicCokernelTopInternalExtIso K E e he M J q hM hAbove).hom =
      (schemeModuleAcyclicCokernelTopInternalExtIso K E e he N I q hN hAbove).hom ≫
        HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (q+1) := by
  let sourceIso := schemeModuleChainOpcycleZeroCokernelIso K ≪≫ e
  have hs : CommSq ((schemeModuleInternalExtFunctor E (q+1)).map c)
      (schemeModuleInternalExtSourceIso sourceIso N (q+1)).inv
      (schemeModuleInternalExtSourceIso sourceIso M (q+1)).inv
      ((schemeModuleInternalExtFunctor (K.opcycles 0) (q+1)).map c) :=
    ⟨schemeModuleInternalExtSourceIso_inv_coefficientNaturality sourceIso c (q+1)⟩
  have ht : CommSq ((schemeModuleInternalExtFunctor (K.opcycles 0) (q+1)).map c)
      (schemeModuleAcyclicChainTopInternalExtIso K
        (schemeModuleCokernelAugmentation_exactAt_succ K E e he) N I q hN hAbove).hom
      (schemeModuleAcyclicChainTopInternalExtIso K
        (schemeModuleCokernelAugmentation_exactAt_succ K E e he) M J q hM hAbove).hom
      (HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (q+1)) :=
    ⟨schemeModuleAcyclicChainTopInternalExtIso_coefficientNaturality K
      (schemeModuleCokernelAugmentation_exactAt_succ K E e he) c I J q hN hM hAbove⟩
  exact (hs.vert_comp ht).w


end LinearStudy
