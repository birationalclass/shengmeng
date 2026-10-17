module
public import Linear.SchemeModuleOriginalNatTargetExt
public import Linear.SchemeModuleOriginalFirstBoundaryCokernel
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
/-- Actual highest internal Ext at ORIGINAL E computed by SAME original differential Hom cokernel. The comparison is CONSTRUCTED from actual source boundaries and derived vanishing,not supplied. -/
def schemeModuleOriginalWholeTopCokernelIso
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (p : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ j q,IsZero (schemeModuleInternalExt (C.X j) N (q+1)))
    (hAbove : IsZero (C.X (p+2))) :
    schemeModuleInternalExt E N (p+1) ≅
      cokernel (schemeModuleHomPrecompose (N := N) (C.d (p+1) p)) := by
  letI := hAlpha
  exact (schemeModuleOriginalNatTargetExtIso C N (p+1) alpha hAlpha).symm ≪≫
    (schemeModuleOriginalNatPositiveTailIso C N (p+1) alpha hAlpha I hA (p+1) (by omega) le_rfl).symm ≪≫
    (schemeModuleChainOpcycleHomCokernelIso C p
      (originalChainAugmentation_exactAt_succ C alpha p) N I (hA p 0)).symm ≪≫
    schemeModuleChainTopHomCokernelIso C N p hAbove
/-- Opaque exact hom equation for the constructed WHOLE comparison. -/
theorem schemeModuleOriginalWholeTopCokernelIso_hom
    (C : ChainComplex X.Modules ℕ) {E : X.Modules} (N : X.Modules) (p : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ j q,IsZero (schemeModuleInternalExt (C.X j) N (q+1)))
    (hAbove : IsZero (C.X (p+2))) :
    letI := hAlpha
    (schemeModuleOriginalWholeTopCokernelIso C N p alpha hAlpha I hA hAbove).hom =
      (schemeModuleOriginalNatTargetExtIso C N (p+1) alpha hAlpha).inv ≫
      (schemeModuleOriginalNatPositiveTailIso C N (p+1) alpha hAlpha I hA (p+1) (by omega) le_rfl).inv ≫
      (schemeModuleChainOpcycleHomCokernelIso C p
        (originalChainAugmentation_exactAt_succ C alpha p) N I (hA p 0)).inv ≫
      (schemeModuleChainTopHomCokernelIso C N p hAbove).hom := rfl
/-- FULL original global Ext class,under actual canonical lambda followed by constructed whole comparison,gives EXACT SAME highest functional modulo ORIGINAL differential. All ranks p+1,not a degree-one specialization. -/
theorem schemeModuleOriginalSmallClass_wholeTopCokernel
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (p : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (I : InjectiveResolution N)
    (hA : ∀ j q,IsZero (schemeModuleInternalExt (C.X j) N (q+1)))
    (hAbove : IsZero (C.X (p+2)))
    (a : C.X (p+1) ⟶ N) (ha : C.d (p+2) (p+1) ≫ a = 0) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleGlobalToInternalExtAll E N (p+1)
        (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a ha) ≫
      (schemeModuleOriginalWholeTopCokernelIso C N p alpha hAlpha I hA hAbove).hom =
        (schemeModuleHomUnitAddEquiv (C.X (p+1)) N).symm a ≫
          cokernel.π (schemeModuleHomPrecompose (N := N) (C.d (p+1) p)) := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  have hclass :
      schemeModuleGlobalToInternalExtAll E N (p+1)
          (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a ha) =
        schemeModuleHomToInternalExtZero (C.opcycles (p+1)) N
            (C.descOpcycles a (p+2) (by simp) ha) ≫
          schemeModuleOriginalNatIteratedBoundary C N (p+1) alpha hAlpha (p+1) ≫
            (schemeModuleOriginalNatTargetExtIso C N (p+1) alpha hAlpha).hom := by
    rw [schemeModuleOriginalNatTargetExtIso_hom]
    exact schemeModuleOriginalSmallClass_nativeIterationImage C (p+1) (by omega) alpha hAlpha a ha
  calc
    _ = schemeModuleHomToInternalExtZero (C.opcycles (p+1)) N
            (C.descOpcycles a (p+2) (by simp) ha) ≫
        schemeModuleInternalExtSourceBoundaryViaResolution (schemeModuleChainOpcycleSequence C p)
          (schemeModuleChainOpcycleSequence_shortExact C p
            (originalChainAugmentation_exactAt_succ C alpha p)) N I 0 ≫
        (schemeModuleChainOpcycleHomCokernelIso C p
          (originalChainAugmentation_exactAt_succ C alpha p) N I (hA p 0)).inv ≫
        (schemeModuleChainTopHomCokernelIso C N p hAbove).hom := by
      rw [hclass,schemeModuleOriginalWholeTopCokernelIso_hom,
        schemeModuleOriginalNatIteratedBoundary_factor C N p alpha hAlpha I hA]
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
    _ = _ := schemeModuleOriginalAugmentedFirstBoundary_cokernel C alpha p N I (hA p 0) hAbove a ha
end LinearStudy
