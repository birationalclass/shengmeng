module
public import Linear.SchemeModuleChainOpcycleExtShift
public import Linear.SchemeModuleHomCokernelCoefficientNaturality
public import Mathlib.CategoryTheory.CommSq
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The SAME final actual Hom-cokernel/Ext1 inverse commutes with coefficients. -/
theorem schemeModuleChainOpcycleHomCokernelIso_inv_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (p : ℕ) (hK : K.ExactAt (p+1))
    {N M : X.Modules} (c : N ⟶ M) (I : InjectiveResolution N) (J : InjectiveResolution M)
    (hN : IsZero (schemeModuleInternalExt (K.X p) N 1))
    (hM : IsZero (schemeModuleInternalExt (K.X p) M 1)) :
    (schemeModuleInternalExtFunctor (K.opcycles p) 1).map c ≫
        (schemeModuleChainOpcycleHomCokernelIso K p hK M J hM).inv =
      (schemeModuleChainOpcycleHomCokernelIso K p hK N I hN).inv ≫
        schemeModuleHomSourceCokernelCoefficientMap (schemeModuleChainOpcycleSequence K p) c := by
  let a := schemeModuleChainOpcycleHomCokernelIso K p hK N I hN
  let b := schemeModuleChainOpcycleHomCokernelIso K p hK M J hM
  have hs : CommSq
      (schemeModuleHomSourceCokernelCoefficientMap (schemeModuleChainOpcycleSequence K p) c)
      a.hom b.hom ((schemeModuleInternalExtFunctor (K.opcycles p) 1).map c) := by
    exact ⟨schemeModuleHomSourceBoundaryCokernelIso_coefficientNaturality
      (schemeModuleChainOpcycleSequence K p) (schemeModuleChainOpcycleSequence_shortExact K p hK)
      c I J hN hM⟩
  exact (CommSq.vert_inv (g := a) (h := b) hs).w

end LinearStudy
