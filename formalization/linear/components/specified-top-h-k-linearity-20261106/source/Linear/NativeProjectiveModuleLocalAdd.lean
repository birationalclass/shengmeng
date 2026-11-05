module
public import Linear.NativeProjectiveModuleLocalPredicate
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S D : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)

/-- The sum of two actual degree-k fractions, restricted to their
common open, has a single common denominator and the same degree k. -/
theorem nativeProjectiveModuleFraction_add
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
    (k : ℤ) {U V : Opens (ProjectiveSpectrum.top 𝓑)}
    {a : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    {b : ∀ p : V, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (ha : nativeProjectiveModuleIsFraction 𝓑 𝒟 k a)
    (hb : nativeProjectiveModuleIsFraction 𝓑 𝒟 k b) :
    nativeProjectiveModuleIsFraction 𝓑 𝒟 k
      (fun p : (U ⊓ V : Opens _) => a ⟨p.1,p.2.1⟩ + b ⟨p.1,p.2.2⟩) := by
  rcases ha with ⟨na,⟨ella,hella⟩,⟨ba,hba⟩,hna,hfa⟩
  rcases hb with ⟨nb,⟨ellb,hellb⟩,⟨bb,hbb⟩,hnb,hfb⟩
  have h1 : bb • ella ∈ 𝒟 (((na+nb : ℕ) : ℤ)+k) := by
    simpa only [Int.natCast_add,add_assoc,add_comm,add_left_comm]
      using hgrade nb ((na : ℤ)+k) bb hbb ella hella
  have h2 : ba • ellb ∈ 𝒟 (((na+nb : ℕ) : ℤ)+k) := by
    simpa only [Int.natCast_add,add_assoc,add_comm,add_left_comm]
      using hgrade na ((nb : ℤ)+k) ba hba ellb hellb
  refine ⟨na+nb,⟨bb • ella+ba • ellb,(𝒟 _).add_mem h1 h2⟩,
    ⟨ba*bb,SetLike.mul_mem_graded hba hbb⟩,?_,?_⟩
  · intro p
    exact p.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hna ⟨p.1,p.2.1⟩) (hnb ⟨p.1,p.2.2⟩)
  · intro p
    dsimp only
    erw [hfa,hfb]
    erw [LocalizedModule.mk_add_mk]
    rfl

/-- Actual local homogeneous-fraction sections are closed under addition.
The gluing step reuses mathlib's local-predicate sheafification theorem. -/
theorem nativeProjectiveModuleLocalPredicate_add
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
    (k : ℤ) {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {a b : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (ha : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred a)
    (hb : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred b) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred (a+b) :=
  PrelocalPredicate.sheafify_inductionOn₂'
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k)
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k)
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k)
    (fun a b => a+b)
    (fun ha hb => nativeProjectiveModuleFraction_add 𝓑 𝒟 hgrade k ha hb) ha hb

theorem nativeProjectiveModuleFraction_neg (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {a : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (ha : nativeProjectiveModuleIsFraction 𝓑 𝒟 k a) :
    nativeProjectiveModuleIsFraction 𝓑 𝒟 k (-a) := by
  rcases ha with ⟨n,ell,b,hb,hf⟩
  refine ⟨n,-ell,b,hb,?_⟩
  intro p
  change -a p = LocalizedModule.mk (-(ell : D)) ⟨(b : S),hb p⟩
  erw [hf]
  exact LocalizedModule.mk_neg.symm

theorem nativeProjectiveModuleLocalPredicate_neg (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {a : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (ha : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred a) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred (-a) :=
  PrelocalPredicate.sheafify_inductionOn'
    (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k) (fun a => -a)
    (fun ha => nativeProjectiveModuleFraction_neg 𝓑 𝒟 k ha) ha

end LinearStudy
