module
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Support
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u

/-- Every ACTUAL derived MODULE Ext_R^j(R/I,N),with original N arbitrary,
is annihilated by ORIGINAL I. Reuse native derived-Ext scalar action and
original quotient annihilator;no target CM/free/flat/source-exactness input. -/
theorem quotientDerivedModuleExt_ideal_annihilator (R : CommRingCat.{u})
    (I : Ideal R) (N : ModuleCat.{u} R) (j : ℕ) :
    I ≤ Module.annihilator R (Ext.{u} (ModuleCat.of R (R ⧸ I)) N j) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro e
  have hAnn : a ∈ Module.annihilator R (R ⧸ I) := by
    simpa only [Ideal.annihilator_quotient] using ha
  have hz := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
    (M := N) (N := ModuleCat.of R (R ⧸ I)) hAnn j
  have hv := congrArg (fun f => f e) hz
  simpa [Ext.mk₀_smul] using hv

/-- Actual MODULE Ext support in EVERY degree is contained in SAME
original closed cut V(I),with no finite-generation condition on N. -/
theorem quotientDerivedModuleExt_support_subset (R : CommRingCat.{u})
    (I : Ideal R) (N : ModuleCat.{u} R) (j : ℕ) :
    Module.support R (Ext.{u} (ModuleCat.of R (R ⧸ I)) N j) ⊆
      PrimeSpectrum.zeroLocus (I : Set R) := by
  intro p hp
  exact (quotientDerivedModuleExt_ideal_annihilator R I N j).trans
    (Module.annihilator_le_of_mem_support hp)

/-- If SAME original closed cut has finite underlying support,EVERY
actual MODULE Ext degree has finite support,for arbitrary original N.
Applying this to SHEAF cohomology still needs its actual comparison. -/
theorem quotientDerivedModuleExt_support_finite (R : CommRingCat.{u})
    (I : Ideal R) (N : ModuleCat.{u} R) (j : ℕ)
    (hI : (PrimeSpectrum.zeroLocus (I : Set R)).Finite) :
    (Module.support R (Ext.{u} (ModuleCat.of R (R ⧸ I)) N j)).Finite :=
  hI.subset (quotientDerivedModuleExt_support_subset R I N j)

end LinearStudy
