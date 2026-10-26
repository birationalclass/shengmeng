module
public import Linear.SchemeModuleHomZeroBoundaryCokernel
public import Linear.SchemeModuleChainOpcycleExtShift
public import Linear.SchemeModuleChainTopOpcycleIso
public import Linear.SchemeModuleHomUnitSourceNaturality
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
/-- The ACTUAL first source boundary of SAME top functional has EXACT original differential-Hom cokernel representative a;no desired representative equality is an input. -/
theorem schemeModuleOriginalFirstBoundary_cokernel
    (C : ChainComplex X.Modules ℕ) (p : ℕ) (hC : C.ExactAt (p+1))
    (N : X.Modules) (I : InjectiveResolution N)
    (hB : IsZero (schemeModuleInternalExt (C.X p) N 1)) (hAbove : IsZero (C.X (p+2)))
    (a : C.X (p+1) ⟶ N) (ha : C.d (p+2) (p+1) ≫ a = 0) :
    schemeModuleHomToInternalExtZero (C.opcycles (p+1)) N
        (C.descOpcycles a (p+2) (by simp) ha) ≫
      schemeModuleInternalExtSourceBoundaryViaResolution (schemeModuleChainOpcycleSequence C p)
        (schemeModuleChainOpcycleSequence_shortExact C p hC) N I 0 ≫
      (schemeModuleChainOpcycleHomCokernelIso C p hC N I hB).inv ≫
      (schemeModuleChainTopHomCokernelIso C N p hAbove).hom =
      (schemeModuleHomUnitAddEquiv (C.X (p+1)) N).symm a ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) (C.d (p+1) p)) := by
  let abar := C.descOpcycles a (p+2) (by simp) ha
  have h := schemeModuleHomZeroBoundary_cokernel (schemeModuleChainOpcycleSequence C p)
    (schemeModuleChainOpcycleSequence_shortExact C p hC) N I hB abar
  have ht := schemeModuleChainTopHomCokernelIso_hom C N p hAbove
  calc
    _ = (schemeModuleHomUnitAddEquiv (C.opcycles (p+1)) N).symm abar ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) (C.fromOpcycles (p+1) p)) ≫
          (schemeModuleChainTopHomCokernelIso C N p hAbove).hom := by
      convert! congrArg
        (fun z => z ≫ (schemeModuleChainTopHomCokernelIso C N p hAbove).hom) h using 1 <;>
          simp only [Category.assoc]
    _ = (schemeModuleHomUnitAddEquiv (C.opcycles (p+1)) N).symm abar ≫
        schemeModuleHomPrecompose (N := N) (C.pOpcycles (p+1)) ≫
          cokernel.π (schemeModuleHomPrecompose (N := N) (C.d (p+1) p)) := by
      rw [ht]
    _ = _ := by
      rw [← Category.assoc,← schemeModuleHomUnitAddEquiv_symm_precompose]
      dsimp only [abar]
      rw [HomologicalComplex.p_descOpcycles]
/-- SAME actual original augmentation DERIVES the needed source exactness before the first-boundary cokernel calculation. -/
theorem schemeModuleOriginalAugmentedFirstBoundary_cokernel
    (C : ChainComplex X.Modules ℕ) {E : X.Modules}
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) [QuasiIso alpha]
    (p : ℕ) (N : X.Modules) (I : InjectiveResolution N)
    (hB : IsZero (schemeModuleInternalExt (C.X p) N 1)) (hAbove : IsZero (C.X (p+2)))
    (a : C.X (p+1) ⟶ N) (ha : C.d (p+2) (p+1) ≫ a = 0) :
    schemeModuleHomToInternalExtZero (C.opcycles (p+1)) N
        (C.descOpcycles a (p+2) (by simp) ha) ≫
      schemeModuleInternalExtSourceBoundaryViaResolution (schemeModuleChainOpcycleSequence C p)
        (schemeModuleChainOpcycleSequence_shortExact C p (originalChainAugmentation_exactAt_succ C alpha p)) N I 0 ≫
      (schemeModuleChainOpcycleHomCokernelIso C p (originalChainAugmentation_exactAt_succ C alpha p) N I hB).inv ≫
      (schemeModuleChainTopHomCokernelIso C N p hAbove).hom =
      (schemeModuleHomUnitAddEquiv (C.X (p+1)) N).symm a ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) (C.d (p+1) p)) :=
  schemeModuleOriginalFirstBoundary_cokernel C p (originalChainAugmentation_exactAt_succ C alpha p)
    N I hB hAbove a ha
end LinearStudy
