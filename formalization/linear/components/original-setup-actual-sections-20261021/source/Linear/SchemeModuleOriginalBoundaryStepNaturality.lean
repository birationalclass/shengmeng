module
public import Linear.SchemeModuleOriginalBoundaryEmbeddingExplicit
public import Linear.SchemeModuleOriginalNatBoundaryStep
public import Linear.SchemeModuleOriginalOpcycleExtComparison
public import Linear.SchemeModuleCochainInternalBoundaryStep
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
/-- EACH actual original Nat-chain boundary commutes with SAME original negative-cochain boundary,including every explicit source index transport. No desired step square is supplied. -/
theorem schemeModuleOriginalBoundaryStep_naturality
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) (n : ℕ) :
    letI := hAlpha
    schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha n ≫
        schemeModuleOriginalOpcycleExtComparison C N r (n+1) =
      schemeModuleOriginalOpcycleExtComparison C N r n ≫
        schemeModuleCochainInternalBoundaryStep (originalChainAsCochain C) N r
          (originalChainAugmentationAsCochain C alpha) n := by
  letI := hAlpha
  by_cases hn : n < r
  · rw [schemeModuleOriginalNatBoundaryStep_eq C N r alpha hAlpha n hn,
      schemeModuleOriginalOpcycleExtComparison_eq C N r (n+1) (by omega),
      schemeModuleOriginalOpcycleExtComparison_eq C N r n (by omega),
      schemeModuleCochainInternalBoundaryStep_eq (originalChainAsCochain C) N r
        (originalChainAugmentationAsCochain C alpha) n hn]
    have hp : -((r-(n+1) : ℕ) : ℤ)=cochainSourceDegree r n+1 := by
      rw [cochainSourceDegree_eq]
      omega
    have h := schemeModuleOriginalOpcycleBoundary_embedding_explicit C alpha N
      (cochainSourceDegree r n) (r-(n+1)) hp n
    have hc := congrArg
      (fun z => eqToHom (congrArg (fun k => schemeModuleInternalExt (C.opcycles k) N n)
        (by omega : r-n=(r-(n+1))+1)) ≫ z) h
    simp only [← Category.assoc] at hc
    rw [schemeModuleOriginalOpcycleExtSourceMap_index C N n
      (cochainSourceDegree r n) (r-n) ((r-(n+1))+1)
      (by rw [cochainSourceDegree_eq]; omega)
      (by rw [cochainSourceDegree_eq]; omega) (by omega)] at hc
    exact hc
  · rw [schemeModuleOriginalNatBoundaryStep_eq_zero C N r alpha hAlpha n hn]
    have hz : schemeModuleCochainInternalBoundaryStep (originalChainAsCochain C) N r
        (originalChainAugmentationAsCochain C alpha) n = 0 := by
      rw [schemeModuleCochainInternalBoundaryStep,dif_neg hn]
    rw [hz,zero_comp,comp_zero]
end LinearStudy
