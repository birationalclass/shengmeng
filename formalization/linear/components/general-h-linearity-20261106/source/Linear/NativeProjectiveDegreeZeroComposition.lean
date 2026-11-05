module
public import Linear.NativeProjectiveDegreeZeroMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable [AddCommGroup F] [Module S F] [Module K F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Composition of the original localized module maps at an actual
projective prime is localization of their original composition. -/
theorem nativeProjectiveModuleAtPrimeMap_comp_apply
    (a : D →ₗ[S] E) (b : E →ₗ[S] F) (p : ProjectiveSpectrum 𝓑)
    (x : nativeProjectiveModuleAtPrime (D := D) 𝓑 p) :
    nativeProjectiveModuleAtPrimeMap 𝓑 b p (nativeProjectiveModuleAtPrimeMap 𝓑 a p x) =
      nativeProjectiveModuleAtPrimeMap 𝓑 (b.comp a) p x := by
  induction x using LocalizedModule.induction_on with
  | h x den =>
    rw [nativeProjectiveModuleAtPrimeMap_mk, nativeProjectiveModuleAtPrimeMap_mk,
      nativeProjectiveModuleAtPrimeMap_mk]
    rfl

variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ) + d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n : ℤ) + d))
variable (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n : ℤ) + d))

/-- Native degree-zero associated-sheaf maps respect actual composition.
No abstract sheafification functor is supplied as an assumption. -/
theorem nativeProjectiveDegreeZeroSheafMap_comp
    (a : D →ₗ[S] E) (b : E →ₗ[S] F)
    (ha : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → a x ∈ ℰ d)
    (hb : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d) (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE a ha k ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hb k =
        nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℱ hD hF (b.comp a)
          (fun d x hx => hb d (a x) (ha d x hx)) k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  exact nativeProjectiveModuleAtPrimeMap_comp_apply 𝓑 a b p.1 (x.1 p)

end LinearStudy
