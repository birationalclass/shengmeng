module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Category.Grp.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
variable {K H V : Type u} [Field K] [AddCommGroup H] [AddCommGroup V] [Module K V]
/-- Convert an actual abelian-group isomorphism to its SAME additive map. -/
def actualAbelianIsoAddEquiv (e : AddCommGrpCat.of H ≅ AddCommGrpCat.of (Module.Dual K V)) :
    H ≃+ Module.Dual K V :=
  AddMonoidHom.toAddEquiv e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)
/-- The additive dual comparison produces an actual pairing,linear in V. -/
def additiveDualComparisonPairing (e : H ≃+ Module.Dual K V) : H →+ Module.Dual K V := e.toAddMonoidHom
/-- The resulting evaluation pairing is left nondegenerate,no perfection
certificate is supplied beyond the already constructed actual dual iso. -/
theorem additiveDualComparisonPairing_left_nondegenerate (e : H ≃+ Module.Dual K V) (h : H)
    (hz : ∀ v,additiveDualComparisonPairing e h v=0) : h=0 := by
  apply e.injective
  change e h=e 0
  rw [map_zero]
  apply LinearMap.ext
  exact hz
/-- The resulting pairing is right nondegenerate by mathlib dual separation.
No finite-dimensionality or additional nondegeneracy premise is used. -/
theorem additiveDualComparisonPairing_right_nondegenerate (e : H ≃+ Module.Dual K V) (v : V)
    (hz : ∀ h,additiveDualComparisonPairing e h v=0) : v=0 := by
  apply (Module.forall_dual_apply_eq_zero_iff K v).mp
  intro f
  obtain ⟨h,rfl⟩ := e.surjective f
  exact hz h
end LinearStudy
