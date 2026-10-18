module
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Linear.CochainResolutionInjectiveCocycle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Actual successive source quotient sequence of SAME complex. -/
def cochainOpcycleSourceSequence (K : CochainComplex A ℤ) (j : ℤ) :
    ShortComplex A :=
  ShortComplex.mk (K.fromOpcycles j (j+1)) (K.pOpcycles (j+1)) (by
    apply (cancel_epi (K.pOpcycles j)).1
    rw [← Category.assoc,K.p_fromOpcycles,K.d_pOpcycles,comp_zero])

/-- SAME original quotient projection is a UNIVERSAL cokernel of the
induced source map,using native opcycles and its epi projection. -/
def cochainOpcycleSourceSequenceIsCokernel (K : CochainComplex A ℤ) (j : ℤ) :
    IsColimit (CokernelCofork.ofπ (cochainOpcycleSourceSequence K j).g
      (cochainOpcycleSourceSequence K j).zero) :=
  CokernelCofork.isColimitOfIsColimitOfIff'
    (K.opcyclesIsCokernel j (j+1) (by simp)) (K.fromOpcycles j (j+1)) (by
      intro W t
      rw [← cancel_epi (K.pOpcycles j),← Category.assoc,K.p_fromOpcycles,comp_zero])

/-- Source exactness DERIVES short exactness of SAME quotient sequence. -/
theorem cochainOpcycleSourceSequence_shortExact (K : CochainComplex A ℤ)
    (j : ℤ) (hK : K.ExactAt j) :
    (cochainOpcycleSourceSequence K j).ShortExact := by
  have hm : Mono (K.fromOpcycles j (j+1)) :=
    Preadditive.mono_of_isZero_kernel' _ (K.homologyIsKernel j (j+1) (by simp)) hK.isZero_homology
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _
      (cochainOpcycleSourceSequenceIsCokernel K j)
    mono_f := hm
    epi_g := inferInstanceAs (Epi (K.pOpcycles (j+1))) }

/-- SAME actual augmentation quasi-isomorphism derives exactness in EVERY
negative source degree,without a new source-exactness certificate. -/
theorem cochainAugmentation_exactAt_negative
    (K : CochainComplex A ℤ) {E : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (j : ℤ) (hj : j < 0) : K.ExactAt j := by
  apply (exactAt_iff_of_quasiIsoAt alpha j).mpr
  exact HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 E j (by omega)

end LinearStudy
