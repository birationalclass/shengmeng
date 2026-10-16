module
public import Linear.NativeProjectiveDegreeZeroComposition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module K D] [Module S D]
variable [AddCommGroup E] [Module K E] [Module S E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n:ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n:ℤ)+d))

/-- The ORIGINAL zero module map is the zero map on actual fraction sheaves. -/
theorem nativeProjectiveDegreeZeroSheafMap_zero (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE (0:D →ₗ[S] E)
      (fun d _ _ => (ℰ d).zero_mem) k = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap 𝓑 (0:D →ₗ[S] E) p.1 (x.1 p) = 0
  induction x.1 p using LocalizedModule.induction_on with
  | h x den => rw [nativeProjectiveModuleAtPrimeMap_mk]; exact LocalizedModule.zero_mk den

/-- The ORIGINAL identity is the identity on actual fraction sheaves. -/
theorem nativeProjectiveDegreeZeroSheafMap_id (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 𝒟 hD hD (LinearMap.id:D →ₗ[S] D)
      (fun _ _ hx => hx) k = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.id:D →ₗ[S] D) p.1 (x.1 p) = x.1 p
  induction x.1 p using LocalizedModule.induction_on with
  | h x den => rw [nativeProjectiveModuleAtPrimeMap_mk]; rfl

/-- An ORIGINAL degree-preserving linear equivalence induces an actual
sheaf isomorphism with the SAME original prime-localized values. -/
def nativeProjectiveDegreeZeroEquivIso (e : D ≃ₗ[S] E)
    (he : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d ↔ e x ∈ ℰ d) (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 𝒟 hD k ≅ nativeProjectiveModuleSheaf 𝓑 ℰ hE k where
  hom := nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e.toLinearMap
    (fun d x hx => (he d x).mp hx) k
  inv := nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD e.symm.toLinearMap
    (fun d y hy => (he d (e.symm y)).mpr (by simpa only [e.apply_symm_apply] using hy)) k
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext p
    change nativeProjectiveModuleAtPrimeMap 𝓑 e.symm.toLinearMap p.1
      (nativeProjectiveModuleAtPrimeMap 𝓑 e.toLinearMap p.1 (x.1 p)) = x.1 p
    induction x.1 p using LocalizedModule.induction_on with
    | h x den =>
      rw [nativeProjectiveModuleAtPrimeMap_mk, nativeProjectiveModuleAtPrimeMap_mk]
      simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext p
    change nativeProjectiveModuleAtPrimeMap 𝓑 e.toLinearMap p.1
      (nativeProjectiveModuleAtPrimeMap 𝓑 e.symm.toLinearMap p.1 (x.1 p)) = x.1 p
    induction x.1 p using LocalizedModule.induction_on with
    | h x den =>
      rw [nativeProjectiveModuleAtPrimeMap_mk, nativeProjectiveModuleAtPrimeMap_mk]
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Any ORIGINAL homogeneous zero composite remains zero on actual sheaves.
Only b*a=0 is needed; exactness and grading decompositions are unnecessary. -/
theorem nativeProjectiveDegreeZeroSheafMap_comp_eq_zero
    {F : Type u} [AddCommGroup F] [Module K F] [Module S F]
    (ℱ : ℤ → Submodule K F)
    (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
      ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n:ℤ)+d))
    (a : D →ₗ[S] E) (b : E →ₗ[S] F)
    (ha : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → a x ∈ ℰ d)
    (hb : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d)
    (hz : b.comp a = 0) (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE a ha k ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hb k = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap 𝓑 b p.1
    (nativeProjectiveModuleAtPrimeMap 𝓑 a p.1 (x.1 p)) = 0
  rw [nativeProjectiveModuleAtPrimeMap_comp_apply, hz]
  induction x.1 p using LocalizedModule.induction_on with
  | h x den => rw [nativeProjectiveModuleAtPrimeMap_mk]; exact LocalizedModule.zero_mk den
end LinearStudy
