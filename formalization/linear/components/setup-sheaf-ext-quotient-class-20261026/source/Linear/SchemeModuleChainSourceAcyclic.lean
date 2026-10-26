module
public import Linear.SchemeModuleAcyclicCokernelRankExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Exact source-acyclicity proposition for ACTUAL derived SHEAF Ext;
this names the universal vanishing statement,not an unproved input instance. -/
def schemeModuleChainSourceExtAcyclic (K : ChainComplex X.Modules ℕ) (N : X.Modules) : Prop :=
  ∀ p j, IsZero (schemeModuleInternalExt (K.X p) N (j+1))

/-- Choose native coefficient resolution at ABSTRACT scheme boundary,
then apply PROVED SAME-chain rank comparison. Original applications need
not elaborate the concrete Grothendieck injective-resolution constructor. -/
def schemeModuleAcyclicCokernelRankCanonicalExtIso (K : ChainComplex X.Modules ℕ)
    (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    (N : X.Modules) (r : ℕ) (hr : 0 < r)
    (hA : schemeModuleChainSourceExtAcyclic K N) (hAbove : IsZero (K.X (r+1))) :
    schemeModuleInternalExt E N r ≅
      (schemeModuleInternalHomCochainComplex N K).homology r :=
  schemeModuleAcyclicCokernelRankInternalExtIso K E e he N (injectiveResolution N) r hr hA hAbove

end LinearStudy
