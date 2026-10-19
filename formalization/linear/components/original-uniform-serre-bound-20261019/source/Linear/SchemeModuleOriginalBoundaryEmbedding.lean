module
public import Linear.SchemeModuleOriginalOpcycleSourceIso
public import Linear.SchemeModuleInternalExtBoundarySourceNaturality
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
/-- Native original cochain/chain identification preserves SAME actual sheaf connecting boundary;all short exactness is DERIVED from SAME augmentation. -/
theorem schemeModuleOriginalOpcycleBoundary_embedding
    (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) [QuasiIso alpha]
    (N : X.Modules) (j : ℤ) (p : ℕ) (h : -(p : ℤ) = j+1) (q : ℕ) :
    schemeModuleInternalExtSourceBoundary (schemeModuleChainOpcycleSequence C p)
        (schemeModuleChainOpcycleSequence_shortExact C p (originalChainAugmentation_exactAt_succ C alpha p)) N q ≫
      schemeModuleInternalExtSourceMap (schemeModuleOriginalOpcycleSourceIso C j p h).hom.τ₃ N (q+1) =
      schemeModuleInternalExtSourceMap (schemeModuleOriginalOpcycleSourceIso C j p h).hom.τ₁ N q ≫
        schemeModuleInternalExtSourceBoundary
          (cochainOpcycleSourceSequence (originalChainAsCochain C) j)
          (cochainOpcycleSourceSequence_shortExact (originalChainAsCochain C) j
            (cochainAugmentation_exactAt_negative (originalChainAsCochain C)
              (originalChainAugmentationAsCochain C alpha) j (by omega))) N q :=
  schemeModuleInternalExtSourceBoundary_sourceNaturality
    (schemeModuleOriginalOpcycleSourceIso C j p h).hom
    (cochainOpcycleSourceSequence_shortExact (originalChainAsCochain C) j
      (cochainAugmentation_exactAt_negative (originalChainAsCochain C)
        (originalChainAugmentationAsCochain C alpha) j (by omega)))
    (schemeModuleChainOpcycleSequence_shortExact C p (originalChainAugmentation_exactAt_succ C alpha p)) N q
end LinearStudy
