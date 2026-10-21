module
public import Linear.AcyclicChainExtVanishing
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- The SAME resolution's actual opcycle zero is its actual target,through native
homology,not a replacement source or assumed cokernel identification. -/
def chainResolutionOpcycleZeroIso (K : ChainComplex A ℕ) (Z : A)
    (f : K ⟶ (ChainComplex.single₀ A).obj Z) [QuasiIso f] : K.opcycles 0 ≅ Z :=
  (K.isoHomologyι 0 0 (by simp) (K.shape 0 0 (by simp))).symm ≪≫
    isoOfQuasiIsoAt f 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 Z
/-- A genuine possibly UNBOUNDED native chain resolution by Ext-acyclic terms
with positive-exact SAME actual Hom cochains has zero positive Ext from its target.
This derives target vanishing;no target-Ext-vanishing or comparison premise. -/
theorem acyclicResolution_ext_subsingleton (K : ChainComplex A ℕ) (Z : A)
    (f : K ⟶ (ChainComplex.single₀ A).obj Z) [QuasiIso f] (F : A)
    (hH : ∀ p, (chainActualHomCochain K F).ExactAt (p+1))
    (hA : ∀ p j, Subsingleton (Ext (K.X p) F (j+1))) (n : ℕ) :
    Subsingleton (Ext Z F (n+1)) := by
  have hK (p : ℕ) : K.ExactAt (p+1) :=
    (exactAt_iff_of_quasiIsoAt f (p+1)).mpr
      (ChainComplex.exactAt_succ_single_obj Z p)
  let e := chainResolutionOpcycleZeroIso K Z f
  letI : Subsingleton (Ext (K.opcycles 0) F (n+1)) :=
    acyclicChainOpcycle_ext_subsingleton K F hK hH hA 0 n
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : (Ext.mk₀ e.hom).comp x (zero_add _) = 0 := Subsingleton.elim _ _
  have h := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add (n+1))) hx
  simpa only [Ext.mk₀_comp_mk₀_assoc,e.inv_hom_id,Ext.mk₀_id_comp,Ext.comp_zero] using h
end LinearStudy
