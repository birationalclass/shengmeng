module
public import Linear.GradedHomComponentNonzero
public import Linear.GradedIntegerProjector
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝓝]

/-- The actual integer-degree part of Hom_A(M,N), defined by its action
on actual homogeneous input elements. -/
def gradedHomPiece (k : ℤ) : Submodule K (M →ₗ[A] N) where
  carrier := {f | ∀ d : ℕ, ∀ x : M, x ∈ ℳ d →
    f x = gradedIntegerProjection 𝓝 ((d : ℤ)+k) (f x)}
  zero_mem' := by intro d x hx; simp
  add_mem' := by
    intro f g hf hg d x hx
    change f x+g x = gradedIntegerProjection 𝓝 ((d : ℤ)+k) (f x+g x)
    rw [map_add,← hf d x hx,← hg d x hx]
  smul_mem' := by
    intro c f hf d x hx
    change c • f x = gradedIntegerProjection 𝓝 ((d : ℤ)+k) (c • f x)
    rw [map_smul,← hf d x hx]

theorem gradedHomComponent_mem_piece (f : M →ₗ[A] N) (k : ℤ) :
    gradedHomComponent 𝒜 ℳ 𝓝 f k ∈ gradedHomPiece ℳ 𝓝 k := by
  intro d x hx
  rw [gradedHomComponent_on_piece 𝒜 ℳ 𝓝 f k d x hx,
    gradedIntegerProjection_projector 𝓝]
  simp

include 𝒜 in
/-- Actual map components are the orthogonal projections of the
actual homogeneous Hom pieces. -/
theorem gradedHomComponent_on_homogeneous_map (j k : ℤ) (f : M →ₗ[A] N)
    (hf : f ∈ gradedHomPiece ℳ 𝓝 k) :
    gradedHomComponent 𝒜 ℳ 𝓝 f j = if j = k then f else 0 := by
  classical
  ext x
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous d x =>
    have hh : (d : ℤ)+j = (d : ℤ)+k ↔ j = k := by omega
    calc
      gradedHomComponent 𝒜 ℳ 𝓝 f j x =
          gradedIntegerProjection 𝓝 ((d : ℤ)+j) (f x) :=
        gradedHomComponent_on_piece 𝒜 ℳ 𝓝 f j d x x.property
      _ = gradedIntegerProjection 𝓝 ((d : ℤ)+j)
          (gradedIntegerProjection 𝓝 ((d : ℤ)+k) (f x)) :=
        congrArg (gradedIntegerProjection 𝓝 ((d : ℤ)+j)) (hf d x x.property)
      _ = (if j = k then f else 0) x := by
        simp only [gradedIntegerProjection_projector 𝓝,hh]
        split_ifs with hjk
        · exact (hf d x x.property).symm
        · rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end LinearStudy
