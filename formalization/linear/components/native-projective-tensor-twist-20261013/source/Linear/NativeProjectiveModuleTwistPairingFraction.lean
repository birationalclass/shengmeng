module
public import Linear.NativeProjectiveModuleTwistSheafOverIso
public import Linear.NativeProjectiveRingModuleLocalization
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
attribute [local instance] LocalizedModule.smulOfIsLocalization
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- The actual ring-module localization acts on the actual module localization
by the original fraction product. -/
theorem nativeProjectiveModuleTwistPairing_prime_mk
    (p : ProjectiveSpectrum 𝓑) (r : S) (ell : M)
    (b c : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p (LocalizedModule.mk r b) •
      LocalizedModule.mk ell c = LocalizedModule.mk (r • ell) (b*c) := by
  rw [nativeProjectiveRingModuleLocalizationEquiv_mk]
  rw [← Localization.mk_eq_mk']
  exact LocalizedModule.mk_smul_mk r ell b c

variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
include hD

/-- A genuine degree-m ring fraction times a degree-k module fraction
is a degree-(k+m) module fraction on the actual common open. -/
theorem nativeProjectiveModuleTwistPairing_fraction (m : ℕ) (k : ℤ)
    {U V : Opens (ProjectiveSpectrum.top 𝓑)}
    {r : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    {ell : ∀ p : V, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1}
    (hr : nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) (m : ℤ) r)
    (hell : nativeProjectiveModuleIsFraction 𝓑 𝒟 k ell) :
    nativeProjectiveModuleIsFraction 𝓑 𝒟 (k+(m : ℤ))
      (fun p : (U ⊓ V : Opens _) =>
        nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r ⟨p.1,p.2.1⟩) •
          ell ⟨p.1,p.2.2⟩) := by
  rcases hr with ⟨nr,r,b,hb,hr⟩
  rcases hell with ⟨nl,ell,c,hc,hell⟩
  have hrn : (r : S) ∈ 𝓑 (nr+m) := by
    simpa only [← Int.natCast_add, nativeProjectiveRingIntegerPiece,
      Int.natCast_nonneg, ite_true, Int.toNat_natCast] using r.property
  have hnum : (r : S) • (ell : M) ∈ 𝒟 (((nr+nl : ℕ) : ℤ)+(k+(m : ℤ))) := by
    simpa only [Int.natCast_add,add_assoc,add_comm,add_left_comm] using
      hD (nr+m) ((nl : ℤ)+k) r hrn ell ell.property
  refine ⟨nr+nl,⟨(r : S) • (ell : M),hnum⟩,
    ⟨(b : S)*(c : S),SetLike.mul_mem_graded b.property c.property⟩,?_,?_⟩
  · intro p
    exact p.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hb ⟨p.1,p.2.1⟩) (hc ⟨p.1,p.2.2⟩)
  · intro p
    dsimp only
    erw [hr,hell]
    exact nativeProjectiveModuleTwistPairing_prime_mk 𝓑 p.1 (r : S) (ell : M)
      ⟨b,hb ⟨p.1,p.2.1⟩⟩ ⟨c,hc ⟨p.1,p.2.2⟩⟩

/-- The fraction pairing preserves the actual sheafified local predicates. -/
theorem nativeProjectiveModuleTwistPairing_local (m : ℕ) (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {r : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    {ell : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1}
    (hr : (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (m : ℤ)).pred r)
    (hell : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred ell) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 (k+(m : ℤ))).pred
      (fun p => nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r p) • ell p) :=
  PrelocalPredicate.sheafify_inductionOn₂'
    (nativeProjectiveModuleFractionPrelocal 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) (m : ℤ))
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k)
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 (k+(m : ℤ)))
    (fun {p} r ell => nativeProjectiveRingModuleLocalizationEquiv 𝓑 p r • ell)
    (fun hr hell => nativeProjectiveModuleTwistPairing_fraction 𝓑 𝒟 hD m k hr hell) hr hell

end LinearStudy
