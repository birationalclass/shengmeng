module
public import Linear.SchemeModuleAcyclicCokernelTopInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Retain exact original positive rank r using EXPLICIT object equality
transports,without expanding opaque homology/cokernel choices. -/
def schemeModuleAcyclicCokernelRankInternalExtIso (K : ChainComplex X.Modules ℕ)
    (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    (N : X.Modules) (I : InjectiveResolution N) (r : ℕ) (hr : 0 < r)
    (hA : ∀ p j, IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (r+1))) :
    schemeModuleInternalExt E N r ≅
      (schemeModuleInternalHomCochainComplex N K).homology r := by
  have h : r-1+1 = r := by omega
  have ha : (r-1)+2 = r+1 := by omega
  have hz : IsZero (K.X ((r-1)+2)) := IsZero.of_iso hAbove (eqToIso (congrArg K.X ha))
  exact eqToIso (congrArg (fun j => schemeModuleInternalExt E N j) h.symm) ≪≫
    schemeModuleAcyclicCokernelTopInternalExtIso K E e he N I (r-1) hA hz ≪≫
    eqToIso (congrArg (fun j => (schemeModuleInternalHomCochainComplex N K).homology j) h)

end LinearStudy
