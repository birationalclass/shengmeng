module
public import Linear.CoextensionIntegralEmbedding
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
variable [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The actual finite domain extension has a functional nonzero on one.
It is constructed by extending to the actual fraction fields and clearing
one denominator on its finitely generated image, not assumed as input. -/
theorem finiteDomainExtension_exists_dual_nonzero :
    ∃ ell : Module.Dual R S, ell 1 ≠ 0 := by
  let K := FractionRing R
  let L := FractionRing S
  obtain ⟨rho,hrho⟩ := Module.Projective.exists_dual_eq_one K (V := L) (one_ne_zero : (1 : L) ≠ 0)
  let f : S →ₗ[R] K := (rho.restrictScalars R).comp ((Algebra.linearMap S L).restrictScalars R)
  have hf1 : f 1 = 1 := by
    change rho (algebraMap S L 1) = 1
    simpa only [map_one] using hrho
  have hfg : (LinearMap.range f).FG := by
    simpa only [Submodule.map_top] using (Module.Finite.fg_top (R := R) (M := S)).map f
  obtain ⟨a,ha,hall⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hfg
  have hane : a ≠ 0 := nonZeroDivisors.ne_zero ha
  let j := Algebra.linearMap R K
  have hj : Function.Injective j := IsFractionRing.injective R K
  let equiv : R ≃ₗ[R] LinearMap.range j := LinearEquiv.ofInjective j hj
  have hrange : ∀ x : S, (a • f) x ∈ LinearMap.range j := fun x => hall (f x) ⟨x,rfl⟩
  let g : S →ₗ[R] LinearMap.range j := (a • f).codRestrict (LinearMap.range j) hrange
  let ell : Module.Dual R S := equiv.symm.toLinearMap.comp g
  have he (x : S) : j (ell x) = a • f x := by
    exact congrArg Subtype.val (equiv.apply_symm_apply (g x))
  have he1 : ell 1 = a := by
    apply hj
    rw [he,hf1]
    simp only [Algebra.smul_def,mul_one]
    rfl
  exact ⟨ell,he1 ▸ hane⟩

/-- Nontriviality of the ACTUAL native dual follows from a constructed
functional of the original finite extension, with its original values. -/
theorem coextensionDual_exists_nonzero_at_one :
    ∃ ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R),
      ell (1 : S) ≠ 0 := by
  obtain ⟨f,hf⟩ := finiteDomainExtension_exists_dual_nonzero (R := R) (S := S)
  let ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) :=
    (coextensionOriginalDualEquiv (R := R) (S := S)).symm f
  refine ⟨ell,?_⟩
  have h := (coextensionOriginalDualEquiv (R := R) (S := S)).apply_symm_apply f
  have hval := congrArg (fun g : Module.Dual R S => g 1) h
  change ell (1 : S) = f 1 at hval
  rw [hval]
  exact hf

end LinearStudy
