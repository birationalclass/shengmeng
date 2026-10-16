module
public import Linear.SchemeModuleChainOpcycleExtShift
public import Mathlib.CategoryTheory.CommSq
public import Linear.SchemeModuleInternalExtSourceBoundaryNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Coefficient square for the SAME actual source dimension-shift inverse.
Both endpoint vanishings are required; the resolution lift is constructed. -/
theorem schemeModuleChainOpcycleExtShiftIso_inv_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (p : ℕ) (hK : K.ExactAt (p+1))
    {N M : X.Modules} (c : N ⟶ M) (I : InjectiveResolution N) (J : InjectiveResolution M)
    (q : ℕ) (hN : ∀ j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hM : ∀ j,IsZero (schemeModuleInternalExt (K.X p) M (j+1))) :
    (schemeModuleInternalExtFunctor (K.opcycles p) (q+2)).map c ≫
        (schemeModuleChainOpcycleExtShiftIso K p hK M J q hM).inv =
      (schemeModuleChainOpcycleExtShiftIso K p hK N I q hN).inv ≫
        (schemeModuleInternalExtFunctor (K.opcycles (p+1)) (q+1)).map c := by
  let a := schemeModuleChainOpcycleExtShiftIso K p hK N I q hN
  let b := schemeModuleChainOpcycleExtShiftIso K p hK M J q hM
  have hs : CommSq
      ((schemeModuleInternalExtFunctor (K.opcycles (p+1)) (q+1)).map c)
      a.hom b.hom ((schemeModuleInternalExtFunctor (K.opcycles p) (q+2)).map c) := by
    constructor
    change _ ≫ (schemeModuleChainOpcycleExtShiftIso K p hK M J q hM).hom =
      (schemeModuleChainOpcycleExtShiftIso K p hK N I q hN).hom ≫ _
    rw [schemeModuleChainOpcycleExtShiftIso_hom,schemeModuleChainOpcycleExtShiftIso_hom]
    exact (schemeModuleInternalExtSourceBoundaryViaResolution_naturality
      (schemeModuleChainOpcycleSequence K p) (schemeModuleChainOpcycleSequence_shortExact K p hK)
      c I J (InjectiveResolution.desc c J I) (InjectiveResolution.desc_commutes_zero c J I) (q+1)).symm
  exact (CommSq.vert_inv (g := a) (h := b) hs).w

end LinearStudy
