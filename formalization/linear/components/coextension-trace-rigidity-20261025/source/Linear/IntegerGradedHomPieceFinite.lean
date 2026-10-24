module
public import Linear.IntegerGradedModuleGenerators
public import Linear.ActualPresentationGradedDualKernel
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
variable {K S M : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
/-- A fixed ORIGINAL Hom degree is finite dimensional when original
coefficient pieces are finite dimensional and the original source is
finite over S. Evaluation on actual homogeneous generators is injective;
no free graded basis,duality certificate or Hom-finiteness input is used. -/
theorem integerGradedHomPiece_finite_of_pieces
    (B : ℕ → Submodule K S) (D : ℤ → Submodule K M)
    [DirectSum.Decomposition D] [Module.Finite S M]
    (hpieces : ∀ j : ℤ, Module.Finite K (nativeProjectiveRingIntegerPiece B j))
    (d : ℤ) : Module.Finite K (integerGradedHomPiece B D d) := by
  classical
  obtain ⟨s,hs,hh⟩ := integerGradedModule_exists_homogeneous_generators (A:=S) D
  let w : s → ℤ := fun i => Classical.choose (hh i i.property)
  have hw (i : s) : (i : M) ∈ D (w i) := Classical.choose_spec (hh i i.property)
  let f : integerGradedHomPiece B D d →ₗ[K]
      (∀ i : s, nativeProjectiveRingIntegerPiece B (w i+d)) :=
    { toFun := fun phi i => ⟨phi.1 i,phi.property (w i) i (hw i)⟩
      map_add' := by intros; funext i; rfl
      map_smul' := by intros; funext i; rfl }
  letI (i : s) : Module.Finite K (nativeProjectiveRingIntegerPiece B (w i+d)) := hpieces _
  apply Module.Finite.of_injective f
  intro phi psi he
  apply Subtype.ext
  apply LinearMap.ext_on hs
  intro x hx
  exact congrArg Subtype.val (congrFun he ⟨x,hx⟩)

/-- Reuses mathlib homogeneousSubmodule_fg;negative ORIGINAL integer
polynomial pieces are zero. Includes every integer degree. -/
theorem polynomialIntegerPiece_finite
    {σ : Type*} [Finite σ] (d : ℤ) :
    Module.Finite K (nativeProjectiveRingIntegerPiece (MvPolynomial.homogeneousSubmodule σ K) d) := by
  by_cases hd : 0 ≤ d
  · rw [nativeProjectiveRingIntegerPiece, if_pos hd]
    exact Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg σ K d.toNat)
  · rw [nativeProjectiveRingIntegerPiece, if_neg hd]
    infer_instance

/-- The actual ORIGINAL homogeneous Hom_R(M,R)_d is finite dimensional
for a finite original integer-graded polynomial module. No homogeneity
of a newly chosen basis or separate finite-dimensionality premise. -/
theorem polynomialIntegerGradedHomPiece_finite
    {σ : Type*} [Finite σ]
    [Module (MvPolynomial σ K) M] [Module.Finite (MvPolynomial σ K) M]
    (D : ℤ → Submodule K M) [DirectSum.Decomposition D] (d : ℤ) :
    Module.Finite K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D d) :=
  integerGradedHomPiece_finite_of_pieces _ D (fun j => polynomialIntegerPiece_finite j) d
end LinearStudy
