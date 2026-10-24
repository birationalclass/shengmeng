module
public import Linear.CoextensionHomInjective
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K S M : Type*} [Field K] [CommRing S] [IsDomain S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M] [IsScalarTower K S M]
variable [SMulCommClass S K M]
/-- Actual degree-zero endomorphisms form the original scalar subalgebra.
Only preservation of the supplied ACTUAL pieces is imposed. -/
def integerGradedEndZero (D : ℤ → Submodule K M) : Subalgebra K (Module.End S M) where
  carrier := {f | ∀ j x,x ∈ D j → f x ∈ D j}
  zero_mem' := by intro j x hx;exact (D j).zero_mem
  one_mem' := by intro j x hx;exact hx
  add_mem' := by intro f g hf hg j x hx;exact (D j).add_mem (hf j x hx) (hg j x hx)
  mul_mem' := by intro f g hf hg j x hx;exact hf j (g x) (hg j x hx)
  algebraMap_mem' := by intro k j x hx;change k • x ∈ D j;exact (D j).smul_mem k hx
/-- Every nonzero endomorphism of an ACTUAL domain-embedded module is
injective. Reuse the existing proved rank-one map theorem,not a new rank
or freeness hypothesis. -/
theorem embeddedDomainModule_nonzero_end_injective
    (e : M →ₗ[S] S) (he : Function.Injective e)
    (f : Module.End S M) (hf : f ≠ 0) : Function.Injective f := by
  have hcomp : e.comp f ≠ 0 := by
    intro h
    apply hf
    ext x
    apply he
    have h' := congrArg (fun g : M →ₗ[S] S => g x) h
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,map_zero] using h'
  have hi := embeddedDomainModule_nonzero_map_injective e he (e.comp f) hcomp
  intro x y hxy
  exact hi (congrArg e hxy)
/-- Degree-zero endomorphisms of the SAME embedded module have no zero
divisors. Finite dimensionality and algebraic closedness are NOT inputs. -/
theorem integerGradedEndZero_noZeroDivisors
    (D : ℤ → Submodule K M) (e : M →ₗ[S] S) (he : Function.Injective e) :
    NoZeroDivisors (integerGradedEndZero (S:=S) D) := by
  constructor
  intro f g hfg
  by_cases hf : f=0
  · exact Or.inl hf
  · right
    have hf' : f.1 ≠ 0 := fun h => hf (Subtype.ext h)
    have hi := embeddedDomainModule_nonzero_end_injective e he f.1 hf'
    apply Subtype.ext
    ext x
    apply hi
    have h := congrArg (fun a : integerGradedEndZero (S:=S) D => a.1 x) hfg
    change f.1 (g.1 x)=0 at h
    change f.1 (g.1 x)=f.1 0
    rw [map_zero]
    exact h
end LinearStudy
