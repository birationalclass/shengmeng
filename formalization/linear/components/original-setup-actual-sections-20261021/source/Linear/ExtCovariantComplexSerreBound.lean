module
public import Linear.ExtCovariantFiniteBiproduct
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Tactic.Linarith
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasFiniteBiproducts A]
/-- Transfer a SINGLE actual twist Serre bound through PRECOMPILED
actual term isomorphisms of SAME C. No concrete complex is expanded
inside opaque Ext. Neither desired acyclicity nor exactness is input. -/
theorem extCovariantComplex_middle_from_Serre_bound
    (C : ChainComplex A ℕ) (O : A) (T : ℤ → A) (N r d : ℕ)
    (e : ∀ p : ℕ,C.X p ≅ biproduct (fun _ : Set.powersetCard (Fin r) p =>
      T ((r : ℤ)*(d : ℤ)-(r : ℤ)-1-(p : ℤ)*(d : ℤ))))
    (hd : N+r+1 ≤ d)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton (Ext O (T s) i)) :
    ∀ j : ℕ,j < r → ∀ i : ℕ,0 < i → Subsingleton (Ext O (C.X (r-j-1)) i) := by
  intro j hj i hi
  let p := r-j-1
  have hp : p < r := by dsimp only [p];omega
  have hpd : (p : ℤ)+1 ≤ (r : ℤ) := by omega
  have hdn : 0 ≤ (d : ℤ) := by omega
  have hbd : (N : ℤ)+(r : ℤ)+1 ≤ (d : ℤ) := by omega
  have hk : (N : ℤ) ≤ (r : ℤ)*(d : ℤ)-(r : ℤ)-1-(p : ℤ)*(d : ℤ) := by nlinarith
  exact ((extFunctorObj O i).mapIso (e p)).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
    (extCovariantFiniteBiproduct_subsingleton O _ i (fun _ => hSerre _ hk i hi))
end LinearStudy
