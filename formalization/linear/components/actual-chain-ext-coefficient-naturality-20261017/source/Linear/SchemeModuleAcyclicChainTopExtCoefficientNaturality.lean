module
public import Linear.SchemeModuleAcyclicChainExtIndependence
public import Linear.SchemeModuleIteratedShiftCoefficientNaturality
public import Linear.SchemeModuleOpcycleHomCoefficientNaturality
public import Linear.SchemeModuleTopHomologyCoefficientNaturality
public import Linear.SchemeModuleAcyclicChainTopHomEquation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The WHOLE SAME top SHEAF Ext comparison commutes with coefficient maps.
Actual augmentation quotients,boundaries,top Hom differential and native cohomology are retained. -/
theorem schemeModuleAcyclicChainTopInternalExtIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (hK : ∀ p,K.ExactAt (p+1))
    {N M : X.Modules} (c : N ⟶ M) (I : InjectiveResolution N) (J : InjectiveResolution M)
    (q : ℕ) (hN : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hM : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) M (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    (schemeModuleInternalExtFunctor (K.opcycles 0) (q+1)).map c ≫
        (schemeModuleAcyclicChainTopInternalExtIso K hK M J q hM hAbove).hom =
      (schemeModuleAcyclicChainTopInternalExtIso K hK N I q hN hAbove).hom ≫
        HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (q+1) := by
  let aN := eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) N 1) (Nat.zero_add q))
  let aM := eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) M 1) (Nat.zero_add q))
  have ha : (schemeModuleInternalExtFunctor (K.opcycles (0+q)) 1).map c ≫ aM.hom =
      aN.hom ≫ (schemeModuleInternalExtFunctor (K.opcycles q) 1).map c :=
    schemeModuleInternalExtSourceIndex_coefficientNaturality (fun z => K.opcycles z) (0+q) q (Nat.zero_add q) c 1
  have ht := schemeModuleChainTopHomologyCokernelIso_coefficientNaturality K q hAbove c
  have hi : schemeModuleChainDifferentialHomCokernelCoefficientMap K q c ≫
      (schemeModuleChainTopHomologyCokernelIso K M q hAbove).inv =
    (schemeModuleChainTopHomologyCokernelIso K N q hAbove).inv ≫
      HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (q+1) := by
    exact (CommSq.vert_inv
      (g := schemeModuleChainTopHomologyCokernelIso K N q hAbove)
      (h := schemeModuleChainTopHomologyCokernelIso K M q hAbove) ⟨ht⟩).w
  have h1 : CommSq ((schemeModuleInternalExtFunctor (K.opcycles 0) (q+1)).map c)
      (schemeModuleChainOpcycleIteratedExtIso K hK N I hN 0 q).hom
      (schemeModuleChainOpcycleIteratedExtIso K hK M J hM 0 q).hom
      ((schemeModuleInternalExtFunctor (K.opcycles (0+q)) 1).map c) :=
    ⟨schemeModuleChainOpcycleIteratedExtIso_coefficientNaturality K hK c I J hN hM 0 q⟩
  have h2 : CommSq ((schemeModuleInternalExtFunctor (K.opcycles (0+q)) 1).map c)
      aN.hom aM.hom ((schemeModuleInternalExtFunctor (K.opcycles q) 1).map c) := ⟨ha⟩
  have h3 : CommSq ((schemeModuleInternalExtFunctor (K.opcycles q) 1).map c)
      (schemeModuleChainOpcycleHomCokernelIso K q (hK q) N I (hN q 0)).inv
      (schemeModuleChainOpcycleHomCokernelIso K q (hK q) M J (hM q 0)).inv
      (schemeModuleHomSourceCokernelCoefficientMap (schemeModuleChainOpcycleSequence K q) c) :=
    ⟨schemeModuleChainOpcycleHomCokernelIso_inv_coefficientNaturality K q (hK q) c I J (hN q 0) (hM q 0)⟩
  have h4 : CommSq (schemeModuleHomSourceCokernelCoefficientMap (schemeModuleChainOpcycleSequence K q) c)
      (schemeModuleChainTopHomCokernelIso K N q hAbove).hom
      (schemeModuleChainTopHomCokernelIso K M q hAbove).hom
      (schemeModuleChainDifferentialHomCokernelCoefficientMap K q c) :=
    ⟨schemeModuleChainTopHomCokernelIso_coefficientNaturality K q hAbove c⟩
  have h5 : CommSq (schemeModuleChainDifferentialHomCokernelCoefficientMap K q c)
      (schemeModuleChainTopHomologyCokernelIso K N q hAbove).inv
      (schemeModuleChainTopHomologyCokernelIso K M q hAbove).inv
      (HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (q+1)) := ⟨hi⟩
  erw [schemeModuleAcyclicChainTopInternalExtIso_hom_equation K hK M J q hM hAbove,
    schemeModuleAcyclicChainTopInternalExtIso_hom_equation K hK N I q hN hAbove]
  exact (h1.vert_comp (h2.vert_comp (h3.vert_comp (h4.vert_comp h5)))).w


end LinearStudy
