module
public import Linear.SchemeModuleAcyclicChainExtIndependence
public import Linear.SchemeModuleIteratedShiftCoefficientNaturality
public import Linear.SchemeModuleOpcycleHomCoefficientNaturality
public import Linear.SchemeModuleTopHomologyCoefficientNaturality
public import Linear.SchemeModuleAcyclicChainTopExtCoefficientNaturality
public import Linear.SchemeModuleExtSourceIsoCoefficientNaturality
public import Linear.SchemeModuleAcyclicCokernelTopExtCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The SAME exact-rank comparison commutes with coefficients through ALL degree casts. -/
theorem schemeModuleAcyclicCokernelRankInternalExtIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    {N M : X.Modules} (c : N ⟶ M) (I : InjectiveResolution N) (J : InjectiveResolution M)
    (r : ℕ) (hr : 0<r) (hN : schemeModuleChainSourceExtAcyclic K N)
    (hM : schemeModuleChainSourceExtAcyclic K M) (hAbove : IsZero (K.X (r+1))) :
    (schemeModuleInternalExtFunctor E r).map c ≫
        (schemeModuleAcyclicCokernelRankInternalExtIso K E e he M J r hr hM hAbove).hom =
      (schemeModuleAcyclicCokernelRankInternalExtIso K E e he N I r hr hN hAbove).hom ≫
        HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) r := by
  have h : r-1+1=r := by omega
  have ha : (r-1)+2=r+1 := by omega
  let hz : IsZero (K.X ((r-1)+2)) := IsZero.of_iso hAbove (eqToIso (congrArg K.X ha))
  have hs := schemeModuleInternalExtDegree_coefficientNaturality E r (r-1+1) h.symm c
  have ht := schemeModuleSourceHomCohomologyDegree_coefficientNaturality K (r-1+1) r h c
  erw [schemeModuleSourceHomCohomologyFunctor_map,schemeModuleSourceHomCohomologyFunctor_map] at ht
  let sN := eqToIso (congrArg (fun j => schemeModuleInternalExt E N j) h.symm)
  let sM := eqToIso (congrArg (fun j => schemeModuleInternalExt E M j) h.symm)
  let tN := eqToIso (congrArg (fun j => (schemeModuleInternalHomCochainComplex N K).homology j) h)
  let tM := eqToIso (congrArg (fun j => (schemeModuleInternalHomCochainComplex M K).homology j) h)
  have h1 : CommSq ((schemeModuleInternalExtFunctor E r).map c)
      sN.hom sM.hom ((schemeModuleInternalExtFunctor E (r-1+1)).map c) := ⟨hs⟩
  have h2 : CommSq ((schemeModuleInternalExtFunctor E (r-1+1)).map c)
      (schemeModuleAcyclicCokernelTopInternalExtIso K E e he N I (r-1) hN hz).hom
      (schemeModuleAcyclicCokernelTopInternalExtIso K E e he M J (r-1) hM hz).hom
      (HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (r-1+1)) :=
    ⟨schemeModuleAcyclicCokernelTopInternalExtIso_coefficientNaturality K E e he c I J (r-1) hN hM hz⟩
  have h3 : CommSq (HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (r-1+1))
      tN.hom tM.hom (HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) r) := ⟨ht⟩
  dsimp only [schemeModuleAcyclicCokernelRankInternalExtIso,Iso.trans_hom]
  exact (h1.vert_comp (h2.vert_comp h3)).w


end LinearStudy
