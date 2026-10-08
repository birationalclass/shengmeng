module
/-
Actual modules for the generator-removal Hilbert--Serre induction.
The kernel and cokernel are finite over the actual smaller adjoined algebra,
because the removed scalar annihilates them.
-/
public import Linear.HilbertFiniteInstances
public import Linear.GradedSubalgebraDecomposition
public import Linear.GradedScalarExactSequence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul 𝒜 ℳ]
variable (d : ℕ) (x : A) (hx : x ∈ 𝒜 d)

theorem gradedScalarKernel_finite_over_adjoin [IsNoetherianRing A] [Module.Finite A M]
    (s : Set A) (hgen : Algebra.adjoin K (insert x s) = ⊤) :
    Module.Finite (Algebra.adjoin K s) (gradedScalarKernel 𝒜 ℳ d x hx).toSubmodule := by
  let p := (gradedScalarKernel 𝒜 ℳ d x hx).toSubmodule
  letI : Module.Finite A p := inferInstance
  apply adjoin_finiteModule_of_annihilator s x hgen
  intro m
  apply Subtype.ext
  exact m.property

theorem gradedScalarCokernel_finite_over_adjoin [Module.Finite A M]
    (s : Set A) (hgen : Algebra.adjoin K (insert x s) = ⊤) :
    Module.Finite (Algebra.adjoin K s) (M ⧸ (gradedScalarImage 𝒜 ℳ d x hx).toSubmodule) := by
  let q := (gradedScalarImage 𝒜 ℳ d x hx).toSubmodule
  apply adjoin_finiteModule_of_annihilator s x hgen
  intro m
  refine Quotient.inductionOn' m ?_
  intro a
  change (Submodule.Quotient.mk (x • a) : M ⧸ q) = 0
  apply (Submodule.Quotient.mk_eq_zero q).mpr
  exact ⟨a, rfl⟩

/-- The restricted kernel's canonical original-ring action. -/
@[instance_reducible] def gradedScalarKernelModule :
    Module A ((gradedScalarKernel 𝒜 ℳ d x hx).toSubmodule.restrictScalars K) := inferInstance

/-- Transport is definitionally the actual original quotient action. -/
@[instance_reducible] def gradedScalarCokernelModule :
    Module A (M ⧸ (gradedScalarImage 𝒜 ℳ d x hx).toSubmodule.restrictScalars K) :=
  inferInstanceAs (Module A (M ⧸ (gradedScalarImage 𝒜 ℳ d x hx).toSubmodule))

attribute [local instance] gradedScalarCokernelModule

theorem gradedScalarKernelGradedSMul : SetLike.GradedSMul 𝒜
    (gradedSubmodulePiece ℳ ((gradedScalarKernel 𝒜 ℳ d x hx).toSubmodule.restrictScalars K)) where
  smul_mem := by
    intro i j a m ha hm
    change a • (m : M) ∈ ℳ (i + j)
    change (m : M) ∈ ℳ j at hm
    exact SetLike.GradedSMul.smul_mem ha hm

theorem gradedScalarCokernelGradedSMul : SetLike.GradedSMul 𝒜
    (gradedQuotientPiece ℳ ((gradedScalarImage 𝒜 ℳ d x hx).toSubmodule.restrictScalars K)) where
  smul_mem := by
    intro i j a m ha hm
    obtain ⟨b, hb, rfl⟩ := hm
    exact ⟨a • b, SetLike.GradedSMul.smul_mem ha hb, rfl⟩

/-- Restrict the actual scalar action to a homogeneous subalgebra. -/
theorem gradedSubalgebraModuleGradedSMul (B : Subalgebra K A) :
    SetLike.GradedSMul (gradedSubalgebraPiece 𝒜 B) ℳ where
  smul_mem := by
    intro i j a m ha hm
    change (a : A) • m ∈ ℳ (i + j)
    change (a : A) ∈ 𝒜 i at ha
    exact SetLike.GradedSMul.smul_mem ha hm

end LinearStudy
