module
/-
Degreewise multiplication exact sequence in the Hilbert--Serre proof.
Adapt the proof route of PR 9819 to actual K-linear submodules, quotients
and mathlib's rank-nullity theorem. No dimension identity is a hypothesis.
-/
public import Linear.GradedQuotientDecomposition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

def gradedScalarMultiplication (n : ℕ) : ℳ n →ₗ[K] ℳ (d + n) where
  toFun m := ⟨x • (m : M), SetLike.GradedSMul.smul_mem hx m.property⟩
  map_add' := by intro a b; ext; exact smul_add x (a : M) (b : M)
  map_smul' := by intro c m; ext; exact smul_comm x c (m : M)

def gradedScalarCokernelPiece (n : ℕ) :=
  gradedQuotientPiece ℳ ((gradedScalarImage 𝒜 ℳ d x hx).toSubmodule.restrictScalars K) n

def gradedScalarCokernelProjection (n : ℕ) : ℳ n →ₗ[K]
    gradedScalarCokernelPiece 𝒜 ℳ d x hx n where
  toFun m := ⟨Submodule.Quotient.mk (m : M), ⟨(m : M), m.property, rfl⟩⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem gradedScalarCokernelProjection_surjective (n : ℕ) :
    Function.Surjective (gradedScalarCokernelProjection 𝒜 ℳ d x hx n) := by
  intro a
  obtain ⟨m, hm, heq⟩ := a.property
  exact ⟨⟨m, hm⟩, Subtype.ext heq⟩

/-- Below the scalar's degree, its image has no homogeneous component. -/
theorem gradedScalarCokernelProjection_injective_of_lt (n : ℕ) (hn : n < d) :
    Function.Injective (gradedScalarCokernelProjection 𝒜 ℳ d x hx n) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro m hm
  let q := (gradedScalarImage 𝒜 ℳ d x hx).toSubmodule.restrictScalars K
  have hm' : (m : M) ∈ q := (Submodule.Quotient.mk_eq_zero q).mp
    (congrArg Subtype.val hm)
  obtain ⟨a, ha⟩ := hm'
  change x • a = (m : M) at ha
  have h := gradedModuleProjection_smul_homogeneous 𝒜 ℳ d n x hx a
  rw [ha, gradedModuleProjection_on_piece ℳ n n m m.property] at h
  apply Subtype.ext
  simpa [Nat.not_le.mpr hn] using h

def gradedScalarCokernelPieceEquiv_of_lt (n : ℕ) (hn : n < d) :
    ℳ n ≃ₗ[K] gradedScalarCokernelPiece 𝒜 ℳ d x hx n :=
  LinearEquiv.ofBijective (gradedScalarCokernelProjection 𝒜 ℳ d x hx n)
    ⟨gradedScalarCokernelProjection_injective_of_lt 𝒜 ℳ d x hx n hn,
      gradedScalarCokernelProjection_surjective 𝒜 ℳ d x hx n⟩

/-- Exactness is derived by projecting an arbitrary preimage to its required degree. -/
theorem gradedScalarMultiplication_exact (n : ℕ) :
    LinearMap.range (gradedScalarMultiplication 𝒜 ℳ d x hx n) =
      LinearMap.ker (gradedScalarCokernelProjection 𝒜 ℳ d x hx (d + n)) := by
  let q := (gradedScalarImage 𝒜 ℳ d x hx).toSubmodule.restrictScalars K
  ext m
  constructor
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    change (Submodule.Quotient.mk (x • (a : M)) : M ⧸ q) = 0
    apply (Submodule.Quotient.mk_eq_zero q).mpr
    exact ⟨(a : M), rfl⟩
  · intro hm
    have hm' : (m : M) ∈ q := (Submodule.Quotient.mk_eq_zero q).mp
      (congrArg Subtype.val hm)
    obtain ⟨a, ha⟩ := hm'
    change x • a = (m : M) at ha
    refine ⟨⟨gradedModuleProjection ℳ n a, (DirectSum.decompose ℳ a n).property⟩, ?_⟩
    apply Subtype.ext
    change x • gradedModuleProjection ℳ n a = (m : M)
    have h := gradedModuleProjection_smul_homogeneous 𝒜 ℳ d (d + n) x hx a
    rw [ha, gradedModuleProjection_on_piece ℳ (d + n) (d + n) m m.property] at h
    simpa using h.symm

def gradedScalarKernelPiece (n : ℕ) :=
  gradedSubmodulePiece ℳ ((gradedScalarKernel 𝒜 ℳ d x hx).toSubmodule.restrictScalars K) n

/-- The actual homogeneous kernel piece equals the kernel of the degreewise map. -/
def gradedScalarKernelPieceEquiv (n : ℕ) :
    gradedScalarKernelPiece 𝒜 ℳ d x hx n ≃ₗ[K]
      LinearMap.ker (gradedScalarMultiplication 𝒜 ℳ d x hx n) where
  toFun m := ⟨⟨m.val.val, m.property⟩, Subtype.ext m.val.property⟩
  invFun m := ⟨⟨m.val.val, congrArg Subtype.val m.property⟩, m.val.property⟩
  left_inv := by intro m; rfl
  right_inv := by intro m; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The Hilbert coefficient identity follows from ACTUAL exactness and rank-nullity. -/
theorem gradedScalar_finrank_recurrence (n : ℕ)
    [Module.Finite K (ℳ n)] [Module.Finite K (ℳ (d + n))] :
    Module.finrank K (ℳ n) + Module.finrank K (gradedScalarCokernelPiece 𝒜 ℳ d x hx (d + n)) =
      Module.finrank K (gradedScalarKernelPiece 𝒜 ℳ d x hx n) + Module.finrank K (ℳ (d + n)) := by
  have h₁ := (gradedScalarMultiplication 𝒜 ℳ d x hx n).finrank_range_add_finrank_ker
  have h₂ := (gradedScalarCokernelProjection 𝒜 ℳ d x hx (d + n)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (gradedScalarCokernelProjection_surjective 𝒜 ℳ d x hx (d + n)),
    finrank_top] at h₂
  rw [← gradedScalarMultiplication_exact 𝒜 ℳ d x hx n] at h₂
  have h₃ := (gradedScalarKernelPieceEquiv 𝒜 ℳ d x hx n).finrank_eq
  omega

end LinearStudy
