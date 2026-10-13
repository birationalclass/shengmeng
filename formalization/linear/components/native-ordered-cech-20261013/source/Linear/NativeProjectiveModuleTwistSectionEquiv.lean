module
public import Linear.NativeProjectiveModuleTwistFraction
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
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Actual positive twist trivialization for any graded module M on EVERY original open set
where a is nonvanishing. Both directions use actual module fractions
and actual native structure-ring actions. -/
def nativeProjectiveModuleTwistSectionEquiv (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    nativeProjectiveModuleSections 𝓑 𝒟
      hD k U ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟
        hD (k+(m : ℤ)) U where
  toFun f := ⟨fun p => nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m (f.1 p),
    nativeProjectiveModuleTwistLocalFraction_forward 𝓑 𝒟 hD a ha m k hp f.property⟩
  invFun f := ⟨fun p => (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f.1 p),
    nativeProjectiveModuleTwistLocalFraction_backward 𝓑 𝒟 hD a ha m k hp f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).apply_symm_apply _
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).map_add _ _
  map_smul' r f := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).map_smul (r.1 p) (f.1 p)

/-- The actual twist trivializations commute with every original open
restriction inside the degree-one chart, including their native ring maps. -/
theorem nativeProjectiveModuleTwistSectionEquiv_restrict (k : ℤ)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (i : U ⟶ V)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (f : nativeProjectiveModuleSections 𝓑 𝒟
      hD k U) :
    (nativeProjectiveModulePresheaf 𝓑 𝒟
      hD (k+(m : ℤ))).map i
        (nativeProjectiveModuleTwistSectionEquiv 𝓑 𝒟 hD a ha m k U hp f) =
      nativeProjectiveModuleTwistSectionEquiv 𝓑 𝒟 hD a ha m k V (fun p => hp (i.unop p))
        ((nativeProjectiveModulePresheaf 𝓑 𝒟
          hD k).map i f) := by
  apply Subtype.ext
  funext p
  rfl

end LinearStudy
