module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- Native covariant boundary is onto when the NEXT actual middle Ext
vanishes. This is relative Ext acyclicity,not global projectivity. -/
theorem relativeAcyclicCovariantBoundary_surjective
    (O : A) {S : ShortComplex A} (hS : S.ShortExact) (n m : ℕ) (hm : n+1=m)
    [Subsingleton (Ext O S.X₂ m)] :
    Function.Surjective (hS.extClass.postcomp O hm) := by
  intro x
  exact Ext.covariant_sequence_exact₁ O hS x (Subsingleton.elim _ _) hm
/-- Native covariant boundary is one-to-one when the PREVIOUS actual
middle Ext vanishes. At degree zero this hypothesis is generally false. -/
theorem relativeAcyclicCovariantBoundary_injective
    (O : A) {S : ShortComplex A} (hS : S.ShortExact) (n m : ℕ) (hm : n+1=m)
    [Subsingleton (Ext O S.X₂ n)] :
    Function.Injective (hS.extClass.postcomp O hm) := by
  intro x y hxy
  have hz : (x-y).comp hS.extClass hm = 0 := by
    change (hS.extClass.postcomp O hm) (x-y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₃ O hS (x-y) hm hz
  have hzero : z = 0 := Subsingleton.elim _ _
  rw [hzero,Ext.zero_comp] at hz
  exact sub_eq_zero.mp hz.symm
end LinearStudy
