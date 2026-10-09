module
public import Linear.GradedIntegerProjector
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 𝓝]

def integerDomainHomComponentAux (f : M →ₗ[A] N) (k : ℤ) : M →ₗ[K] N := by
  classical
  exact (DirectSum.toModule K ℤ N (fun d =>
    (gradedIntegerProjection 𝓝 (d+k)).comp
      ((f.restrictScalars K).comp (𝒟 d).subtype))).comp
    (DirectSum.decomposeLinearEquiv 𝒟).toLinearMap

theorem integerDomainHomComponentAux_on_piece (f : M →ₗ[A] N) (k d : ℤ)
    (x : M) (hx : x ∈ 𝒟 d) :
    integerDomainHomComponentAux 𝒟 𝓝 f k x = gradedIntegerProjection 𝓝 (d+k) (f x) := by
  classical
  change (DirectSum.toModule K ℤ N (fun d =>
    (gradedIntegerProjection 𝓝 (d+k)).comp
      ((f.restrictScalars K).comp (𝒟 d).subtype)))
    (DirectSum.decomposeLinearEquiv 𝒟 x) = _
  rw [show DirectSum.decomposeLinearEquiv 𝒟 x =
    DirectSum.lof K ℤ (fun d => 𝒟 d) d ⟨x,hx⟩ from
      DirectSum.decomposeLinearEquiv_apply_coe 𝒟 d ⟨x,hx⟩]
  rw [DirectSum.toModule_lof]
  rfl

theorem integerDomainHomComponentAux_smul
    (hgrade : ∀ d : ℕ, ∀ a : A, a ∈ 𝒜 d → ∀ j : ℤ, ∀ x : M,
      x ∈ 𝒟 j → a • x ∈ 𝒟 (j+(d : ℤ)))
    (f : M →ₗ[A] N) (k : ℤ) (a : A) (x : M) :
    integerDomainHomComponentAux 𝒟 𝓝 f k (a • x) =
      a • integerDomainHomComponentAux 𝒟 𝓝 f k x := by
  have hhom (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) (x : M) :
      integerDomainHomComponentAux 𝒟 𝓝 f k (a • x) =
        a • integerDomainHomComponentAux 𝒟 𝓝 f k x := by
    induction x using DirectSum.Decomposition.inductionOn 𝒟 with
    | zero => simp
    | @homogeneous j x =>
      rw [integerDomainHomComponentAux_on_piece 𝒟 𝓝 f k (j+(d : ℤ)) (a • (x : M))
        (hgrade d a ha j x x.property),
        integerDomainHomComponentAux_on_piece 𝒟 𝓝 f k j x x.property,
        map_smul,gradedIntegerProjection_smul_homogeneous 𝒜 𝓝 d
          ((j+(d : ℤ))+k) a ha (f x)]
      have hshift : (j+(d : ℤ)+k)-(d : ℤ) = j+k := by omega
      rw [hshift]
    | add x y hx hy => simp only [smul_add,map_add,hx,hy]
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous d a => exact hhom d a a.property x
  | add a b ha hb => simp only [add_smul,map_add,ha,hb]

def integerDomainHomComponent
    (hgrade : ∀ d : ℕ, ∀ a : A, a ∈ 𝒜 d → ∀ j : ℤ, ∀ x : M,
      x ∈ 𝒟 j → a • x ∈ 𝒟 (j+(d : ℤ)))
    (f : M →ₗ[A] N) (k : ℤ) : M →ₗ[A] N where
  toFun := integerDomainHomComponentAux 𝒟 𝓝 f k
  map_add' := map_add (integerDomainHomComponentAux 𝒟 𝓝 f k)
  map_smul' := integerDomainHomComponentAux_smul 𝒜 𝒟 𝓝 hgrade f k

end LinearStudy
