module
public import Linear.SchemeModuleSingleShiftCoefficientNaturality
public import Linear.SchemeModuleExtIndexCoefficientNaturality
public import Linear.SchemeModuleIteratedExtRecursion
public import Linear.SchemeModuleHomCokernelCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ALL successive actual quotient-boundary shifts commute with coefficients. -/
theorem schemeModuleChainOpcycleIteratedExtIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (hK : ∀ p,K.ExactAt (p+1))
    {N M : X.Modules} (c : N ⟶ M) (I : InjectiveResolution N) (J : InjectiveResolution M)
    (hN : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hM : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) M (j+1))) (p q : ℕ) :
    (schemeModuleInternalExtFunctor (K.opcycles p) (q+1)).map c ≫
        (schemeModuleChainOpcycleIteratedExtIso K hK M J hM p q).hom =
      (schemeModuleChainOpcycleIteratedExtIso K hK N I hN p q).hom ≫
        (schemeModuleInternalExtFunctor (K.opcycles (p+q)) 1).map c := by
  induction q generalizing p with
  | zero =>
    rw [schemeModuleChainOpcycleIteratedExtIso_zero K hK M J hM p,
      schemeModuleChainOpcycleIteratedExtIso_zero K hK N I hN p]
    exact (Category.comp_id ((schemeModuleInternalExtFunctor (K.opcycles p) 1).map c)).trans
      (Category.id_comp ((schemeModuleInternalExtFunctor (K.opcycles p) 1).map c)).symm
  | succ q ih =>
    have hp : (p+1)+q = p+(q+1) := by omega
    let aN := eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) N 1) hp)
    let aM := eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) M 1) hp)
    have ha : (schemeModuleInternalExtFunctor (K.opcycles ((p+1)+q)) 1).map c ≫ aM.hom =
        aN.hom ≫ (schemeModuleInternalExtFunctor (K.opcycles (p+(q+1))) 1).map c :=
      schemeModuleInternalExtSourceIndex_coefficientNaturality (fun z => K.opcycles z) ((p+1)+q) (p+(q+1)) hp c 1
    rw [schemeModuleChainOpcycleIteratedExtIso_succ K hK M J hM p q,
      schemeModuleChainOpcycleIteratedExtIso_succ K hK N I hN p q]
    dsimp only [Iso.trans_hom,Iso.symm_hom]
    have hs : CommSq ((schemeModuleInternalExtFunctor (K.opcycles p) (q+2)).map c)
        (schemeModuleChainOpcycleExtShiftIso K p (hK p) N I q (hN p)).inv
        (schemeModuleChainOpcycleExtShiftIso K p (hK p) M J q (hM p)).inv
        ((schemeModuleInternalExtFunctor (K.opcycles (p+1)) (q+1)).map c) :=
      ⟨schemeModuleChainOpcycleExtShiftIso_inv_coefficientNaturality K p (hK p) c I J q (hN p) (hM p)⟩
    have ht : CommSq ((schemeModuleInternalExtFunctor (K.opcycles (p+1)) (q+1)).map c)
        (schemeModuleChainOpcycleIteratedExtIso K hK N I hN (p+1) q).hom
        (schemeModuleChainOpcycleIteratedExtIso K hK M J hM (p+1) q).hom
        ((schemeModuleInternalExtFunctor (K.opcycles ((p+1)+q)) 1).map c) := ⟨ih (p+1)⟩
    have hu : CommSq ((schemeModuleInternalExtFunctor (K.opcycles ((p+1)+q)) 1).map c)
        aN.hom aM.hom ((schemeModuleInternalExtFunctor (K.opcycles (p+(q+1))) 1).map c) := ⟨ha⟩
    exact (hs.vert_comp (ht.vert_comp hu)).w


end LinearStudy
