module
public import Linear.GradedHomComponentNonzero
public import Linear.GradedModuleHomogeneousGenerators
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝓝]

/-- Every actual map out of a finite graded module has only finitely
many nonzero integer-degree components. The bound is constructed from
actual finite homogeneous generators and their actual image components. -/
theorem gradedHomComponent_finite_support [Module.Finite A M] (f : M →ₗ[A] N) :
    ∃ s : Finset ℤ, ∀ k : ℤ, k ∉ s → gradedHomComponent 𝒜 ℳ 𝓝 f k = 0 := by
  classical
  obtain ⟨g,hg,hhom⟩ := finiteModule_exists_homogeneous_generators (A := A) ℳ
  let d (x : g) : ℕ := (hhom x x.property).choose
  have hd (x : g) : (x : M) ∈ ℳ (d x) := (hhom x x.property).choose_spec
  let s : Finset ℤ := g.attach.biUnion fun x =>
    (DirectSum.decompose 𝓝 (f x)).support.image fun (j : ℕ) => (j : ℤ)-(d x : ℤ)
  refine ⟨s,?_⟩
  intro k hk
  have hz (x : M) (hx : x ∈ g) : gradedHomComponent 𝒜 ℳ 𝓝 f k x = 0 := by
    let z : g := ⟨x,hx⟩
    rw [gradedHomComponent_on_piece 𝒜 ℳ 𝓝 f k (d z) x (hd z)]
    unfold gradedIntegerProjection
    by_cases hdk : 0 ≤ (d z : ℤ)+k
    · rw [if_pos hdk]
      have hnot : ((d z : ℤ)+k).toNat ∉ (DirectSum.decompose 𝓝 (f x)).support := by
        intro hm
        apply hk
        apply Finset.mem_biUnion.mpr
        refine ⟨z,Finset.mem_attach _ _,?_⟩
        apply Finset.mem_image.mpr
        refine ⟨((d z : ℤ)+k).toNat,hm,?_⟩
        omega
      have he : DirectSum.decompose 𝓝 (f x) ((d z : ℤ)+k).toNat = 0 := by
        simpa only [DFinsupp.mem_support_iff,not_not] using hnot
      simp only [gradedModuleProjection_apply,he,Submodule.coe_zero]
    · simp only [if_neg hdk,LinearMap.zero_apply]
  have hker : Submodule.span A (g : Set M) ≤ LinearMap.ker (gradedHomComponent 𝒜 ℳ 𝓝 f k) :=
    Submodule.span_le.mpr (fun x hx => hz x hx)
  rw [hg] at hker
  ext x
  exact hker (show x ∈ (⊤ : Submodule A M) from trivial)

end LinearStudy
