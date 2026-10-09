module
public import Linear.FiniteCoextensionModule
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Module.Finite K L]

/-- At an actual finite field extension, the native coextension dual is
a one-dimensional module over the upper field. No trace or separability
assumption is necessary for this field-module assertion. -/
theorem fieldCoextensionDual_exists_equiv :
    Nonempty (L ≃ₗ[L]
      (ModuleCat.coextendScalars (algebraMap K L)).obj (ModuleCat.of K K)) := by
  classical
  let D := (ModuleCat.coextendScalars (algebraMap K L)).obj (ModuleCat.of K K)
  let B := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  let Dr := (ModuleCat.restrictScalars (algebraMap K L)).obj D
  letI : Module.Finite K B := Module.Finite.equiv restrictedAlgebraModuleEquiv.symm
  letI : Module.Finite K Dr := restrictedCoextensionDual_finite
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  let l' : B →ₗ[K] K := l.comp restrictedAlgebraModuleEquiv.toLinearMap
  let ell : D := (ModuleCat.CoextendScalars.equiv (algebraMap K L)
    (ModuleCat.of K K)).symm l'
  have hell : ell ≠ 0 := by
    intro he
    have h' := congrArg (fun v : D => v (1 : L)) he
    change l 1 = 0 at h'
    exact one_ne_zero (hl.symm.trans h')
  let p : L →ₗ[L] D := LinearMap.toSpanSingleton L D ell
  have hp : Function.Injective p :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton (R := L) (M := D) hell)
  let pr : B →ₗ[K] Dr :=
    ((ModuleCat.restrictScalars (algebraMap K L)).map (ModuleCat.ofHom p)).hom
  have hdim : Module.finrank K B = Module.finrank K Dr := by
    rw [(restrictedCoextensionDualEquiv (R := K) (S := L)).finrank_eq]
    exact (Subspace.dual_finrank_eq (K := K) (V := B)).symm
  have hpr : Function.Surjective pr :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hp
  exact ⟨LinearEquiv.ofBijective p ⟨hp,hpr⟩⟩

end LinearStudy
