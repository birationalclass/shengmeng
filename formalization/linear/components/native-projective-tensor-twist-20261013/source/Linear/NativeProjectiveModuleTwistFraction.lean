module
public import Linear.NativeProjectiveModuleTwistUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
variable (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)
include ha hD

/-- Multiplication by a^m takes genuine degree-k module fractions to
actual degree-(k+m) fractions on the same original open. -/
theorem nativeProjectiveModuleTwistFraction_forward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 𝒟 k f) :
    nativeProjectiveModuleIsFraction 𝓑 𝒟 (k+(m : ℤ))
      (fun p => nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m (f p)) := by
  rcases hf with ⟨n,ell,b,hb,hf⟩
  have ham : a^m ∈ 𝓑 m := by simpa using SetLike.pow_mem_graded m ha
  have hnum : a^m • (ell : M) ∈ 𝒟 ((n : ℤ)+(k+(m : ℤ))) := by
    simpa only [add_assoc,add_comm,add_left_comm] using
      hD m ((n : ℤ)+k) (a^m) ham ell ell.property
  refine ⟨n,⟨a^m • (ell : M),hnum⟩,b,hb,?_⟩
  intro p
  dsimp only
  erw [hf]
  exact nativeProjectiveModulePrimeTwistEquiv_mk 𝓑 p.1 a (hp p) m (ell : M) ⟨b,hb p⟩

/-- Dividing a genuine degree-(k+m) module fraction by a^m uses
its actual degree-(n+m) denominator b*a^m, without a supplied certificate. -/
theorem nativeProjectiveModuleTwistFraction_backward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 𝒟 (k+(m : ℤ)) f) :
    nativeProjectiveModuleIsFraction 𝓑 𝒟 k
      (fun p => (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f p)) := by
  rcases hf with ⟨n,ell,b,hb,hf⟩
  have ham : a^m ∈ 𝓑 m := by simpa using SetLike.pow_mem_graded m ha
  have hnum : (ell : M) ∈ 𝒟 (((n+m : ℕ) : ℤ)+k) := by
    simpa only [Int.natCast_add,add_assoc,add_comm,add_left_comm] using ell.property
  refine ⟨n+m,⟨(ell : M),hnum⟩,
    ⟨(b : S)*a^m,SetLike.mul_mem_graded b.property ham⟩,?_,?_⟩
  · intro p
    exact p.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb p)
      (p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hp p) m)
  · intro p
    dsimp only
    erw [hf]
    exact nativeProjectiveModulePrimeTwistEquiv_symm_mk 𝓑 p.1 a (hp p) m (ell : M) ⟨b,hb p⟩

/-- Forward multiplication preserves the actual local-fraction predicate. -/
theorem nativeProjectiveModuleTwistLocalFraction_forward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 (k+(m : ℤ))).pred
      (fun p => nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m (f p)) := by
  intro p
  rcases hf p with ⟨V,hp',i,hf⟩
  exact ⟨V,hp',i,nativeProjectiveModuleTwistFraction_forward 𝓑 𝒟 hD a ha m k
    (fun q => hp (i q)) hf⟩

/-- The constructed inverse also preserves genuine locally homogeneous fractions. -/
theorem nativeProjectiveModuleTwistLocalFraction_backward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 (k+(m : ℤ))).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred
      (fun p => (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f p)) := by
  intro p
  rcases hf p with ⟨V,hp',i,hf⟩
  exact ⟨V,hp',i,nativeProjectiveModuleTwistFraction_backward 𝓑 𝒟 hD a ha m k
    (fun q => hp (i q)) hf⟩

end LinearStudy
