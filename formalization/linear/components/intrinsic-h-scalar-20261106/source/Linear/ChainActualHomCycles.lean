module
public import Linear.AcyclicResolutionGlobalExtCokernel
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- Actual Hom cycles are Hom from native opposite cycles,by the EXISTING
limit-preserving additive Yoneda functor and actual kernel universal property.
No projectivity,Ext acyclicity or desired cohomology comparison is an input. -/
def chainActualHomCyclesNativeIso (K : ChainComplex A ℕ) (F : A) (n : ℕ) :
    (chainActualHomCochain K F).cycles n ≅ (preadditiveYoneda.obj F).obj (K.op.cycles n) :=
  IsLimit.conePointUniqueUpToIso
    ((chainActualHomCochain K F).cyclesIsKernel n (n+1) (by simp))
    (KernelFork.mapIsLimit _ (K.op.cyclesIsKernel n (n+1) (ComplexShape.next_eq' (ComplexShape.down ℕ).symm (by rfl))) (preadditiveYoneda.obj F))
/-- Actual inclusion into Hom term is preserved by the same kernel iso. -/
theorem chainActualHomCyclesNativeIso_inv_iCycles (K : ChainComplex A ℕ) (F : A) (n : ℕ) :
    (chainActualHomCyclesNativeIso K F n).inv ≫ (chainActualHomCochain K F).iCycles n =
      (preadditiveYoneda.obj F).map (K.op.iCycles n) :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    ((chainActualHomCochain K F).cyclesIsKernel n (n+1) (by simp))
    (KernelFork.mapIsLimit _ (K.op.cyclesIsKernel n (n+1) (ComplexShape.next_eq' (ComplexShape.down ℕ).symm (by rfl))) (preadditiveYoneda.obj F))
    WalkingParallelPair.zero
/-- Actual Hom cycles are Hom from SAME original opcycles,using native
opposite-complex comparison rather than replacing the relation object. -/
def chainActualHomCyclesOpcyclesIso (K : ChainComplex A ℕ) (F : A) (n : ℕ) :
    (chainActualHomCochain K F).cycles n ≅ AddCommGrpCat.of (K.opcycles n ⟶ F) :=
  chainActualHomCyclesNativeIso K F n ≪≫ (preadditiveYoneda.obj F).mapIso (K.cyclesOpIso n)
/-- SAME original Hom precomposition into opcycles becomes SAME actual Hom
cochain to-cycles map. Thus the original boundary relation is retained. -/
theorem chainActualHomCyclesOpcyclesIso_boundary (K : ChainComplex A ℕ) (F : A) (p : ℕ) :
    acyclicChainOpcycleHomPrecompose K F p ≫ (chainActualHomCyclesOpcyclesIso K F (p+1)).inv =
      (chainActualHomCochain K F).toCycles p (p+1) := by
  change (preadditiveYoneda.obj F).map (K.fromOpcycles (p+1) p).op ≫
    (chainActualHomCyclesOpcyclesIso K F (p+1)).inv = (chainActualHomCochain K F).toCycles p (p+1)
  apply (cancel_mono ((chainActualHomCochain K F).iCycles (p+1))).1
  dsimp only [chainActualHomCyclesOpcyclesIso,Iso.trans_inv,Functor.mapIso_inv]
  rw [Category.assoc,Category.assoc,chainActualHomCyclesNativeIso_inv_iCycles]
  rw [← Category.assoc,← Functor.map_comp,HomologicalComplex.fromOpcycles_op_cyclesOpIso_inv]
  simp only [← Functor.map_comp,HomologicalComplex.toCycles_i]
  rfl
end LinearStudy
