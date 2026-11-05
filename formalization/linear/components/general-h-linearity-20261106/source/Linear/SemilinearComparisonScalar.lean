module
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u v w uM uN uP
variable {R : Type u} {A : Type v} {B : Type w}
variable [Semiring R] [Semiring A] [Semiring B]
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module A N] [Module B P]
/-- Two actual semilinear bijections out of the SAME module induce an
additive comparison commuting with their two specified scalar maps.
This is a consequence of semilinearity, not an assumed comparison square. -/
theorem semilinear_bijective_comparison_smul
    (sigmaA : R →+* A) (sigmaB : R →+* B)
    (fA : M →ₛₗ[sigmaA] N) (fB : M →ₛₗ[sigmaB] P)
    (hA : Function.Bijective fA) (hB : Function.Bijective fB)
    (r : R) (s : N) :
    ((AddEquiv.ofBijective fA.toAddMonoidHom hA).symm.trans
      (AddEquiv.ofBijective fB.toAddMonoidHom hB)) (sigmaA r • s) =
      sigmaB r • ((AddEquiv.ofBijective fA.toAddMonoidHom hA).symm.trans
        (AddEquiv.ofBijective fB.toAddMonoidHom hB)) s := by
  let eA := AddEquiv.ofBijective fA.toAddMonoidHom hA
  let eB := AddEquiv.ofBijective fB.toAddMonoidHom hB
  obtain ⟨x,rfl⟩ := hA.surjective s
  change eB (eA.symm (sigmaA r • fA x)) = sigmaB r • eB (eA.symm (fA x))
  rw [← fA.map_smulₛₗ r x]
  change fB (eA.symm (eA (r • x))) = sigmaB r • fB (eA.symm (eA x))
  rw [eA.symm_apply_apply,eA.symm_apply_apply]
  exact fB.map_smulₛₗ r x
end LinearStudy
