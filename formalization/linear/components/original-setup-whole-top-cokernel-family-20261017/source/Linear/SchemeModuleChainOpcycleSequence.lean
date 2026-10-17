module
public import Linear.SchemeModuleInternalExtSourceBoundaryCokernel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual successive quotient sequence of SAME original chain complex:
opcycles(p+1)->Kp->opcycles(p). No projectivity is required. -/
def schemeModuleChainOpcycleSequence (K : ChainComplex X.Modules ℕ) (p : ℕ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (K.fromOpcycles (p+1) p) (K.pOpcycles p) (by
    apply (cancel_epi (K.pOpcycles (p+1))).1
    rw [← Category.assoc,K.p_fromOpcycles,K.d_pOpcycles,comp_zero])

/-- SAME original quotient projection is a UNIVERSAL cokernel of the
induced source map,by native actual opcycles cokernel and its epi projection. -/
def schemeModuleChainOpcycleSequenceIsCokernel (K : ChainComplex X.Modules ℕ) (p : ℕ) :
    IsColimit (CokernelCofork.ofπ (schemeModuleChainOpcycleSequence K p).g
      (schemeModuleChainOpcycleSequence K p).zero) :=
  CokernelCofork.isColimitOfIsColimitOfIff'
    (K.opcyclesIsCokernel (p+1) p (by simp)) (K.fromOpcycles (p+1) p) (by
      intro W t
      rw [← cancel_epi (K.pOpcycles (p+1)),← Category.assoc,K.p_fromOpcycles,comp_zero])

/-- Actual positive source exactness DERIVES short exactness of SAME
successive quotient sequence. No desired syzygy short-exactness input. -/
theorem schemeModuleChainOpcycleSequence_shortExact (K : ChainComplex X.Modules ℕ)
    (p : ℕ) (hK : K.ExactAt (p+1)) :
    (schemeModuleChainOpcycleSequence K p).ShortExact := by
  have hm : Mono (K.fromOpcycles (p+1) p) :=
    Preadditive.mono_of_isZero_kernel' _ (K.homologyIsKernel (p+1) p (by simp)) hK.isZero_homology
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _
      (schemeModuleChainOpcycleSequenceIsCokernel K p)
    mono_f := hm
    epi_g := inferInstanceAs (Epi (K.pOpcycles p)) }

end LinearStudy
