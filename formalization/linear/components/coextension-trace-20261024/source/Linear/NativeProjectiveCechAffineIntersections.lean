module
public import Linear.ModuleBaseCechFactors
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Actual basic opens convert any finite product into the intersection
of the original opens. No separatedness certificate is an input. -/
theorem nativeProjective_basicOpen_finset_prod {τ : Type*}
    (s : Finset τ) (f : τ → S) :
    Proj.basicOpen 𝓑 (∏ k ∈ s, f k) = ⨅ k ∈ s, Proj.basicOpen 𝓑 (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      simp only [Finset.prod_insert hk, Proj.basicOpen_mul, ih,
        Finset.iInf_insert]

variable {ι : Type u} (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)

/-- Every actual Cech intersection of degree-one opens is the original
native basic open for their product. -/
theorem nativeProjective_cechIntersection_eq_basicOpen (n : ℕ)
    (i : Fin (n+1) → ι) :
    (∏ᶜ fun k : Fin (n+1) => Proj.basicOpen 𝓑 (a (i k))) =
      Proj.basicOpen 𝓑 (∏ k : Fin (n+1), a (i k)) := by
  rw [show (∏ᶜ fun k : Fin (n+1) => Proj.basicOpen 𝓑 (a (i k))) =
      ⨅ k : Fin (n+1), Proj.basicOpen 𝓑 (a (i k)) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  simpa using (nativeProjective_basicOpen_finset_prod 𝓑
    (Finset.univ : Finset (Fin (n+1))) (fun k => a (i k))).symm

include ha in
/-- The original coordinate product is homogeneous of its actual
positive degree n+1. The degree follows from graded multiplication. -/
theorem nativeProjective_cechProduct_mem_degree (n : ℕ)
    (i : Fin (n+1) → ι) :
    (∏ k : Fin (n+1), a (i k)) ∈ 𝓑 (n+1) := by
  simpa using (SetLike.prod_mem_graded 𝓑 (fun _ : Fin (n+1) => (1 : ℕ))
    (fun k => a (i k)) (F := Finset.univ) (fun k _ => ha (i k)))

include ha in
/-- Every actual intersection in the degree-one native Cech family
is affine. This is derived from the actual positive-degree chart,
without assuming Proj separatedness or intersection affineness. -/
theorem nativeProjective_cechIntersection_isAffine (n : ℕ)
    (i : Fin (n+1) → ι) :
    IsAffineOpen (∏ᶜ fun k : Fin (n+1) => Proj.basicOpen 𝓑 (a (i k))) := by
  rw [nativeProjective_cechIntersection_eq_basicOpen 𝓑 a n i]
  exact Proj.isAffineOpen_basicOpen 𝓑 _
    (nativeProjective_cechProduct_mem_degree 𝓑 a ha n i) (Nat.zero_lt_succ n)

end LinearStudy
