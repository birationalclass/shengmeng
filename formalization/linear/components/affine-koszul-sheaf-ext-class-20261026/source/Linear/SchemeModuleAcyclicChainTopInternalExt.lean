module
public import Linear.SchemeModuleChainOpcycleExtShift
public import Linear.SchemeModuleChainTopOpcycleIso
public import Linear.SchemeModuleChainTopHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL top SHEAF Ext of SAME degree-zero quotient is top cohomology
of SAME actual internal-Hom complex. Derived from actual successive source
boundaries,not global projectivity or an assumed Ext-comparison. -/
def schemeModuleAcyclicChainTopInternalExtIso (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p, K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (q : ℕ) (hA : ∀ p j, IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    schemeModuleInternalExt (K.opcycles 0) N (q+1) ≅
      (schemeModuleInternalHomCochainComplex N K).homology (q+1) := by
  exact schemeModuleChainOpcycleIteratedExtIso K hK N I hA 0 q ≪≫
    eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) N 1)
      (Nat.zero_add q)) ≪≫
    (schemeModuleChainOpcycleHomCokernelIso K q (hK q) N I (hA q 0)).symm ≪≫
    schemeModuleChainTopHomCokernelIso K N q hAbove ≪≫
    (schemeModuleChainTopHomologyCokernelIso K N q hAbove).symm

end LinearStudy
