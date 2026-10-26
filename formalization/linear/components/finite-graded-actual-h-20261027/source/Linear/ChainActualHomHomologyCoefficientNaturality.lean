module
public import Linear.ChainActualHomCoefficientNaturality
public import Linear.AcyclicHomCokernelCoefficientNaturality
public import Linear.AcyclicResolutionGlobalExtHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
/-- The SAME native homology-to-Hom-cokernel comparison takes actual
homology projection to original opcycle-Hom quotient projection. -/
theorem chainActualHomCochainHomologyCokernelIso_projection
    (K : ChainComplex A ℕ) (F : A) (p : ℕ) :
    (chainActualHomCochain K F).homologyπ (p+1) ≫
      (chainActualHomCochainHomologyCokernelIso K F p).hom =
      (chainActualHomCyclesOpcyclesIso K F (p+1)).hom ≫
        cokernel.π (acyclicChainOpcycleHomPrecompose K F p) := by
  let H := chainActualHomCochain K F
  have hπ := IsColimit.comp_coconePointUniqueUpToIso_inv
    (cokernelIsCokernel (H.toCycles p (p+1)))
    (H.homologyIsCokernel p (p+1) (by simp)) WalkingParallelPair.one
  change H.homologyπ (p+1) ≫
    ((cokernelIsCokernel (H.toCycles p (p+1))).coconePointUniqueUpToIso
      (H.homologyIsCokernel p (p+1) (by simp))).inv = cokernel.π (H.toCycles p (p+1)) at hπ
  dsimp only [H] at hπ
  dsimp only [chainActualHomCochainHomologyCokernelIso,Iso.trans_hom,Iso.symm_hom]
  erw [← Category.assoc,hπ]
  exact cokernel.π_desc _ _ _
/-- The SAME actual Hom-cochain homology/cokernel comparison is natural
in coefficients;native homologyMap and quotient maps are retained. -/
theorem chainActualHomCochainHomologyCokernelIso_coefficient_naturality
    (K : ChainComplex A ℕ) {F G : A} (a : F ⟶ G) (p : ℕ) :
    HomologicalComplex.homologyMap (chainActualHomCochainCoefficientMap K a) (p+1) ≫
      (chainActualHomCochainHomologyCokernelIso K G p).hom =
      (chainActualHomCochainHomologyCokernelIso K F p).hom ≫
        acyclicChainOpcycleHomCokernelCoefficientMap K a p := by
  apply (cancel_epi ((chainActualHomCochain K F).homologyπ (p+1))).1
  rw [← Category.assoc,HomologicalComplex.homologyπ_naturality,
    Category.assoc,chainActualHomCochainHomologyCokernelIso_projection,
    ← Category.assoc,chainActualHomCyclesOpcyclesIso_coefficient_naturality,
    Category.assoc,← acyclicChainOpcycleHomCokernelCoefficientMap_projection,
    ← Category.assoc,← chainActualHomCochainHomologyCokernelIso_projection]
  simp only [Category.assoc]
end LinearStudy
