module
public import Linear.SchemeModuleOriginalBoundaryEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] originalChainAugmentationAsCochain_quasiIso
universe u
variable {X : Scheme.{u}}
/-- Expose SAME native original source isomorphisms without re-expanding short-complex proof fields. -/
theorem schemeModuleOriginalOpcycleBoundary_embedding_explicit
    (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) [QuasiIso alpha]
    (N : X.Modules) (j : ℤ) (p : ℕ) (h : -(p : ℤ)=j+1) (q : ℕ) :
    schemeModuleInternalExtSourceBoundary (schemeModuleChainOpcycleSequence C p)
        (schemeModuleChainOpcycleSequence_shortExact C p (originalChainAugmentation_exactAt_succ C alpha p)) N q ≫
      schemeModuleInternalExtSourceMap (originalChainAsCochainOpcyclesIso C (j+1) p h).hom N (q+1) =
      schemeModuleInternalExtSourceMap (originalChainAsCochainOpcyclesIso C j (p+1) (by omega)).hom N q ≫
        schemeModuleInternalExtSourceBoundary
          (cochainOpcycleSourceSequence (originalChainAsCochain C) j)
          (cochainOpcycleSourceSequence_shortExact (originalChainAsCochain C) j
            (cochainAugmentation_exactAt_negative (originalChainAsCochain C)
              (originalChainAugmentationAsCochain C alpha) j (by omega))) N q :=
  schemeModuleOriginalOpcycleBoundary_embedding C alpha N j p h q
end LinearStudy
