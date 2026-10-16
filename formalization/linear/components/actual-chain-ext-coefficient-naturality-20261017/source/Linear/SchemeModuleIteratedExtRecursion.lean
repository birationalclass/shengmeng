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

/-- Opaque recursion equation prevents re-expanding derived boundary proofs in coefficient squares. -/
theorem schemeModuleChainOpcycleIteratedExtIso_zero (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p,K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1))) (p : ℕ) :
    schemeModuleChainOpcycleIteratedExtIso K hK N I hA p 0 = Iso.refl _ := rfl

/-- SAME actual iterated comparison retains its native recursive boundary and index transport. -/
theorem schemeModuleChainOpcycleIteratedExtIso_succ (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p,K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1))) (p q : ℕ) :
    schemeModuleChainOpcycleIteratedExtIso K hK N I hA p (q+1) =
      (schemeModuleChainOpcycleExtShiftIso K p (hK p) N I q (hA p)).symm ≪≫
        schemeModuleChainOpcycleIteratedExtIso K hK N I hA (p+1) q ≪≫
          eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) N 1)
            (by omega : (p+1)+q=p+(q+1))) := rfl

end LinearStudy
