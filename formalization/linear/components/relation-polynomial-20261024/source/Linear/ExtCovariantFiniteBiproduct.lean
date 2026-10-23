module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- ACTUAL GLOBAL relative Ext vanishing survives finite biproducts in
its COEFFICIENT variable. This is not internal SHEAF Ext vanishing. -/
theorem extCovariantFiniteBiproduct_subsingleton
    (O : A) {ι : Type w'} [Fintype ι] (P : ι → A) [HasBiproduct P]
    (q : ℕ) (hv : ∀ i,Subsingleton (Ext O (P i) q)) :
    Subsingleton (Ext O (biproduct P) q) := by
  let F := extFunctorObj O q
  let D := Discrete.functor P
  have hz : IsZero (D ⋙ F) := (D ⋙ F).isZero_iff.mpr (fun i => by
    change IsZero (AddCommGrpCat.of (Ext O (P i.as) q))
    haveI := hv i.as
    exact AddCommGrpCat.isZero_of_subsingleton _)
  exact AddCommGrpCat.subsingleton_of_isZero
    ((isLimitOfPreserves F (biproduct.isLimit P)).isZero_pt hz)
end LinearStudy
