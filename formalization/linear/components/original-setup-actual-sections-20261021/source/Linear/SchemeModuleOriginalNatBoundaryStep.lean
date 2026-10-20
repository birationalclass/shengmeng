module
public import Linear.SchemeModuleOriginalOpcycleSourceIso
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
/-- SAME actual original Nat-chain source boundaries,starting from the original top quotient;explicit arithmetic transport is retained. Outside n<r the extension is zero and unused. -/
def schemeModuleOriginalNatBoundaryStep (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (N : X.Modules) (r : ℕ) (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
    (hAlpha : QuasiIso alpha) (n : ℕ) :
    schemeModuleInternalExt (C.opcycles (r-n)) N n ⟶
      schemeModuleInternalExt (C.opcycles (r-(n+1))) N (n+1) := by
  letI := hAlpha
  exact if hn : n < r then
    eqToHom (congrArg (fun z => schemeModuleInternalExt (C.opcycles z) N n)
      (by omega : r-n=(r-(n+1))+1)) ≫
      schemeModuleInternalExtSourceBoundary (schemeModuleChainOpcycleSequence C (r-(n+1)))
        (schemeModuleChainOpcycleSequence_shortExact C (r-(n+1))
          (originalChainAugmentation_exactAt_succ C alpha (r-(n+1)))) N n
  else 0
/-- Used degree is EXACT SAME original source boundary with explicit source-index transport. -/
theorem schemeModuleOriginalNatBoundaryStep_eq (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (N : X.Modules) (r : ℕ) (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
    (hAlpha : QuasiIso alpha) (n : ℕ) (hn : n < r) :
    letI := hAlpha
    schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha n =
      eqToHom (congrArg (fun z => schemeModuleInternalExt (C.opcycles z) N n)
        (by omega : r-n=(r-(n+1))+1)) ≫
      schemeModuleInternalExtSourceBoundary (schemeModuleChainOpcycleSequence C (r-(n+1)))
        (schemeModuleChainOpcycleSequence_shortExact C (r-(n+1))
          (originalChainAugmentation_exactAt_succ C alpha (r-(n+1)))) N n := by
  letI := hAlpha
  rw [schemeModuleOriginalNatBoundaryStep,dif_pos hn]
/-- Zero extension outside USED finite range;no extra source exactness is introduced. -/
theorem schemeModuleOriginalNatBoundaryStep_eq_zero (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (N : X.Modules) (r : ℕ) (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
    (hAlpha : QuasiIso alpha) (n : ℕ) (hn : ¬ n < r) :
    schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha n = 0 := by
  rw [schemeModuleOriginalNatBoundaryStep,dif_neg hn]
end LinearStudy
