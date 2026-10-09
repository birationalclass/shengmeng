module
public import Linear.NativeProjectivePrimeTwistUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)
include ha

/-- Multiplication by a^m sends actual degree-k homogeneous fractions
to degree-(k+m) fractions wherever the degree-one element a is nonzero. -/
theorem nativeProjectiveTwistFraction_forward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) k f) :
    nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) (k+(m : ℤ))
      (fun p => nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m (f p)) := by
  rcases hf with ⟨n,ell,b,hb,hf⟩
  have ham : a^m ∈ 𝓑 m := by simpa using SetLike.pow_mem_graded m ha
  have hnum : a^m*(ell : S) ∈
      nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ)+(k+(m : ℤ))) := by
    simpa only [smul_eq_mul,add_assoc,add_comm,add_left_comm] using
      nativeProjectiveRingIntegerPiece_graded 𝓑 m ((n : ℤ)+k) (a^m) ham ell ell.property
  refine ⟨n,⟨a^m*(ell : S),hnum⟩,b,hb,?_⟩
  intro p
  dsimp only
  erw [hf]
  exact nativeProjectivePrimeTwistEquiv_mk 𝓑 p.1 a (hp p) m ell ⟨b,hb p⟩

/-- The inverse twist map uses the actual homogeneous denominator b*a^m;
the numerator's integer degree then becomes the required degree-k degree. -/
theorem nativeProjectiveTwistFraction_backward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (k+(m : ℤ)) f) :
    nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) k
      (fun p => (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f p)) := by
  rcases hf with ⟨n,ell,b,hb,hf⟩
  have ham : a^m ∈ 𝓑 m := by simpa using SetLike.pow_mem_graded m ha
  have hnum : (ell : S) ∈ nativeProjectiveRingIntegerPiece 𝓑 (((n+m : ℕ) : ℤ)+k) := by
    simpa only [Int.natCast_add,add_assoc,add_comm,add_left_comm] using ell.property
  refine ⟨n+m,⟨(ell : S),hnum⟩,
    ⟨(b : S)*a^m,SetLike.mul_mem_graded b.property ham⟩,?_,?_⟩
  · intro p
    exact p.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb p)
      (p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hp p) m)
  · intro p
    dsimp only
    erw [hf]
    exact nativeProjectivePrimeTwistEquiv_symm_mk 𝓑 p.1 a (hp p) m ell ⟨b,hb p⟩

theorem nativeProjectiveTwistLocalFraction_forward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) k).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (k+(m : ℤ))).pred
      (fun p => nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m (f p)) := by
  intro p
  rcases hf p with ⟨V,hp',i,hf⟩
  exact ⟨V,hp',i,nativeProjectiveTwistFraction_forward 𝓑 a ha m k (fun q => hp (i q)) hf⟩

theorem nativeProjectiveTwistLocalFraction_backward (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (k+(m : ℤ))).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) k).pred
      (fun p => (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f p)) := by
  intro p
  rcases hf p with ⟨V,hp',i,hf⟩
  exact ⟨V,hp',i,nativeProjectiveTwistFraction_backward 𝓑 a ha m k (fun q => hp (i q)) hf⟩

end LinearStudy
