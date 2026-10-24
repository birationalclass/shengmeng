module
public import Linear.OriginalChainOpcycleEmbedding
public import Linear.CochainOpcycleSourceSequence
public import Linear.SchemeModuleChainOpcycleSequence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- SAME source short exact sequence before/after the original n-to-minus-n conversion,retaining actual maps in ALL three terms. -/
def schemeModuleOriginalOpcycleSourceIso (C : ChainComplex X.Modules ℕ)
    (j : ℤ) (p : ℕ) (h : -(p : ℤ) = j+1) :
    cochainOpcycleSourceSequence (originalChainAsCochain C) j ≅
      schemeModuleChainOpcycleSequence C p :=
  ShortComplex.isoMk
    (originalChainAsCochainOpcyclesIso C j (p+1) (by omega))
    (originalChainAsCochainXIso C (j+1) p h)
    (originalChainAsCochainOpcyclesIso C (j+1) p h)
    (originalChainAsCochain_fromOpcycles C j (j+1) (p+1) p (by omega) h).symm
    (originalChainAsCochain_pOpcycles C (j+1) p h).symm
/-- SAME original quasi-isomorphic augmentation derives every positive chain exactness condition. -/
theorem originalChainAugmentation_exactAt_succ (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) [QuasiIso alpha] (p : ℕ) :
    C.ExactAt (p+1) := by
  apply (exactAt_iff_of_quasiIsoAt alpha (p+1)).mpr
  exact HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0 E (p+1) (by omega)
end LinearStudy
