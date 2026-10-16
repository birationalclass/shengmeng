module
public import Linear.SchemeModuleAcyclicChainTopInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- Exact SAME top comparison hom equation;use this proved equation to
avoid repeatedly expanding source-boundary construction proofs. -/
theorem schemeModuleAcyclicChainTopInternalExtIso_hom_equation
    (K : ChainComplex X.Modules ℕ) (hK : ∀ p,K.ExactAt (p+1))
    (N : X.Modules) (I : InjectiveResolution N) (q : ℕ)
    (hA : ∀ p j,IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    (schemeModuleAcyclicChainTopInternalExtIso K hK N I q hA hAbove).hom =
      (schemeModuleChainOpcycleIteratedExtIso K hK N I hA 0 q).hom ≫
      (eqToIso (congrArg (fun z => schemeModuleInternalExt (K.opcycles z) N 1) (Nat.zero_add q))).hom ≫
      (schemeModuleChainOpcycleHomCokernelIso K q (hK q) N I (hA q 0)).inv ≫
      (schemeModuleChainTopHomCokernelIso K N q hAbove).hom ≫
      (schemeModuleChainTopHomologyCokernelIso K N q hAbove).inv := rfl

end LinearStudy
