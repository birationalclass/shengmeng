module
public import Linear.SchemeModuleAcyclicChainTopInternalExt
public import Linear.SchemeModuleFiniteFreeFrameInternalExt
public import Linear.ChainActualCokernelTargetAugmentation
public import Mathlib.Algebra.Homology.SingleHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- SAME actual opcycles0 quotient compared with SAME categorical coker d1. -/
def schemeModuleChainOpcycleZeroCokernelIso (K : ChainComplex X.Modules ℕ) :
    K.opcycles 0 ≅ cokernel (K.d 1 0) :=
  (K.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
    (colimit.isColimit (parallelPair (K.d 1 0) 0))

/-- The SAME quotient projection is retained by zero-opcycles/cokernel iso. -/
theorem schemeModuleChainOpcycleZeroCokernelIso_projection (K : ChainComplex X.Modules ℕ) :
    K.pOpcycles 0 ≫ (schemeModuleChainOpcycleZeroCokernelIso K).hom =
      cokernel.π (K.d 1 0) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (K.opcyclesIsCokernel 1 0 (by simp)) (colimit.isColimit (parallelPair (K.d 1 0) 0)) .one

/-- A SAME actual quotient-target augmentation quasiiso DERIVES positive
source exactness;desired exactness is not separately assumed. -/
theorem schemeModuleCokernelAugmentation_exactAt_succ (K : ChainComplex X.Modules ℕ)
    (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e)) (p : ℕ) :
    K.ExactAt (p+1) := by
  letI := he
  exact (exactAt_iff_of_quasiIsoAt
    (originalChainCokernelTargetAugmentation K E e) (p+1)).2
      (ChainComplex.exactAt_succ_single_obj E p)

/-- Actual top derived SHEAF Ext of SAME augmentation target is SAME
original Hom-complex top cohomology. Keep actual cokernel iso,its SAME
quotient augmentation and its actual quasiiso certificate throughout. -/
def schemeModuleAcyclicCokernelTopInternalExtIso (K : ChainComplex X.Modules ℕ)
    (E : X.Modules) (e : cokernel (K.d 1 0) ≅ E)
    (he : QuasiIso (originalChainCokernelTargetAugmentation K E e))
    (N : X.Modules) (I : InjectiveResolution N) (q : ℕ)
    (hA : ∀ p j, IsZero (schemeModuleInternalExt (K.X p) N (j+1)))
    (hAbove : IsZero (K.X (q+2))) :
    schemeModuleInternalExt E N (q+1) ≅
      (schemeModuleInternalHomCochainComplex N K).homology (q+1) :=
  (schemeModuleInternalExtSourceIso (schemeModuleChainOpcycleZeroCokernelIso K ≪≫ e)
    N (q+1)).symm ≪≫ schemeModuleAcyclicChainTopInternalExtIso K
      (schemeModuleCokernelAugmentation_exactAt_succ K E e he) N I q hA hAbove

end LinearStudy
