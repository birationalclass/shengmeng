module
public import Linear.SchemeModuleOriginalBoundaryStepNaturality
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Linear.SchemeModuleCochainIteratedInternalBoundary
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
/-- Native sequence natural transformation built from PROVED SAME original source-boundary squares,not an assumed iteration identity. -/
def schemeModuleOriginalBoundarySequenceComparison
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) :
    letI := hAlpha
    Functor.ofSequence (schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha) ⟶
      Functor.ofSequence (schemeModuleCochainInternalBoundaryStep (originalChainAsCochain C) N r
        (originalChainAugmentationAsCochain C alpha)) := by
  letI := hAlpha
  refine NatTrans.ofSequence (fun n => schemeModuleOriginalOpcycleExtComparison C N r n) ?_
  intro n
  rw [Functor.ofSequence_map_homOfLE_succ,Functor.ofSequence_map_homOfLE_succ]
  exact schemeModuleOriginalBoundaryStep_naturality C N r alpha hAlpha n
/-- SAME actual original Nat-chain sequence map over a finite initial interval. -/
def schemeModuleOriginalNatIteratedBoundary
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha) (n : ℕ) :
    schemeModuleInternalExt (C.opcycles r) N 0 ⟶
      schemeModuleInternalExt (C.opcycles (r-n)) N n :=
  Functor.OfSequence.map (schemeModuleOriginalNatBoundaryStep C N r alpha hAlpha) 0 n (Nat.zero_le n)
/-- FULL finite iteration commutes with SAME original quotient comparison,at EVERY used degree including both endpoints. -/
theorem schemeModuleOriginalBoundaryIteration_naturality
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (n : ℕ) (hn : n ≤ r) :
    letI := hAlpha
    schemeModuleOriginalNatIteratedBoundary C N r alpha hAlpha n ≫
        schemeModuleOriginalOpcycleExtComparison C N r n =
      schemeModuleOriginalOpcycleExtComparison C N r 0 ≫
        schemeModuleCochainIteratedInternalBoundary (originalChainAsCochain C) N r
          (originalChainAugmentationAsCochain C alpha) n hn := by
  letI := hAlpha
  have h := (schemeModuleOriginalBoundarySequenceComparison C N r alpha hAlpha).naturality
    (homOfLE (Nat.zero_le n))
  exact h
end LinearStudy
