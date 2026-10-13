module
public import Linear.CoextensionFractionEmbedding
public import Linear.FiniteCoextensionUpper
public import Mathlib.RingTheory.FractionalIdeal.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- All actual dual elements have one common nonzero denominator,
derived from finite generation of their image in the actual fraction field. -/
theorem coextensionDual_exists_common_denominator :
    ∃ a : S, a ≠ 0 ∧ ∀ ell :
      (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R),
      IsLocalization.IsInteger S (a • coextensionFractionEmbedding (R := R) (S := S) ell) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let E := coextensionFractionEmbedding (R := R) (S := S)
  letI : Module.Finite S D := coextensionDual_finite_upper
  have hfg : (LinearMap.range E).FG := by
    simpa only [Submodule.map_top] using
      (Module.Finite.fg_top (R := S) (M := D)).map E
  obtain ⟨a,ha,hall⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors S) hfg
  exact ⟨a,nonZeroDivisors.ne_zero ha,fun ell => hall (E ell) ⟨ell,rfl⟩⟩

/-- The actual finite-normalization dual admits an actual upper-ring
linear injection into that ring. A generic embedding or common denominator
is not an input; both are constructed from the original algebra. -/
theorem coextensionDual_exists_integral_embedding :
    ∃ e : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) →ₗ[S] S,
      Function.Injective e := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let E := coextensionFractionEmbedding (R := R) (S := S)
  obtain ⟨a,ha,hall⟩ := coextensionDual_exists_common_denominator (R := R) (S := S)
  let j := Algebra.linearMap S (FractionRing S)
  have hj : Function.Injective j := IsFractionRing.injective S (FractionRing S)
  let equiv : S ≃ₗ[S] LinearMap.range j := LinearEquiv.ofInjective j hj
  have hrange : ∀ ell : D, (a • E) ell ∈ LinearMap.range j := by
    intro ell
    exact hall ell
  let F : D →ₗ[S] LinearMap.range j := (a • E).codRestrict (LinearMap.range j) hrange
  let e : D →ₗ[S] S := equiv.symm.toLinearMap.comp F
  have he (ell : D) : j (e ell) = a • E ell := by
    have h := equiv.apply_symm_apply (F ell)
    exact congrArg Subtype.val h
  refine ⟨e,?_⟩
  intro x y hxy
  apply coextensionFractionEmbedding_injective (R := R) (S := S)
  have hmul : algebraMap S (FractionRing S) a * E x =
      algebraMap S (FractionRing S) a * E y := by
    simpa only [Algebra.smul_def] using
      (he x).symm.trans ((congrArg j hxy).trans (he y))
  have haF : algebraMap S (FractionRing S) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr ha
  exact mul_left_cancel₀ haF hmul

end LinearStudy
