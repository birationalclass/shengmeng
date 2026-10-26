module
public import Linear.ChainActualHomCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- Actual positive Hom-cochain homology is the SAME original Hom/opcycles
cokernel,using actual native cycles,actual differential and native quotient.
No projectivity,Ext acyclicity or desired homology comparison premise. -/
def chainActualHomCochainHomologyCokernelIso (K : ChainComplex A ℕ) (F : A) (p : ℕ) :
    (chainActualHomCochain K F).homology (p+1) ≅ cokernel (acyclicChainOpcycleHomPrecompose K F p) :=
  ((cokernelIsCokernel ((chainActualHomCochain K F).toCycles p (p+1))).coconePointUniqueUpToIso
    ((chainActualHomCochain K F).homologyIsCokernel p (p+1) (by simp))).symm ≪≫
      cokernel.mapIso _ _ (Iso.refl _) (chainActualHomCyclesOpcyclesIso K F (p+1)) (by
        rw [← chainActualHomCyclesOpcyclesIso_boundary,Category.assoc,
          Iso.inv_hom_id,Category.comp_id,Iso.refl_hom,Category.id_comp])
variable [CategoryTheory.HasExt.{v} A]
/-- An actual acyclic resolution computes positive GLOBAL Ext by ACTUAL
Hom-cochain homology. Uses SAME original resolution and additive Yoneda
maps,without assuming comparison,projectivity or coefficient injectivity.
The construction records unsigned Yoneda normalization;standard signed
connecting-map compatibility remains a separate obligation. -/
def acyclicResolutionGlobalExtActualHomologyIso
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] (F : A)
    (hA : ∀ p j,Subsingleton (CategoryTheory.Abelian.Ext (K.X p) F (j+1))) (q : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Abelian.Ext Z F (q+1)) ≅
      (chainActualHomCochain K F).homology (q+1) :=
  acyclicResolutionGlobalExtHomCokernelIso K Z f F hA q ≪≫
    (chainActualHomCochainHomologyCokernelIso K F q).symm
end LinearStudy
