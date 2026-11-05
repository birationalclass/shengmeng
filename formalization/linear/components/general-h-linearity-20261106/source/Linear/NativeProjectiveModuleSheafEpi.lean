module
public import Linear.NativeProjectiveModuleFractionLift
public import Mathlib.Topology.Sheaves.LocallySurjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : E, ell ∈ ℰ d → b • ell ∈ ℰ ((n : ℤ)+d))
variable (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+0))
variable (hpre : ∀ d : ℤ, ∀ ell : E, ell ∈ ℰ d →
  ∃ x : D, x ∈ 𝒟 d ∧ e x = ell)
include hpre

/-- Actual homogeneous numerator lifts give local surjectivity of
the actual native Proj associated-module presheaf morphism. -/
theorem nativeProjectiveModulePresheafMap_isLocallySurjective (k : ℤ) :
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝓑))
      (nativeProjectiveModulePresheafMap 𝓑 𝒟 ℰ hD hE 0 e hh k) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U f p hp
  let ff : nativeProjectiveModuleSections 𝓑 ℰ hE (k+0) (op U) := f
  have hf := ff.property
  change (nativeProjectiveModuleLocalPredicate 𝓑 ℰ (k+0)).pred ff.1 at hf
  simp only [add_zero] at hf
  rcases hf ⟨p,hp⟩ with ⟨V,hpV,i,hfrac⟩
  obtain ⟨g,hg,heq⟩ := nativeProjectiveModuleFraction_lifts 𝓑 𝒟 ℰ e hpre k hfrac
  have hglocal : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred g :=
    fun q => ⟨V,q.property,𝟙 V,hg⟩
  let s : nativeProjectiveModuleSections 𝓑 𝒟 hD k (op V) := ⟨g,hglocal⟩
  refine ⟨V,i.le,⟨s,?_⟩,hpV⟩
  apply Subtype.ext
  funext q
  exact heq q

/-- Actual homogeneous surjections induce epimorphisms of genuine
associated module SHEAVES on the original native Proj. -/
theorem nativeProjectiveModuleSheafMap_epi (k : ℤ) :
    Epi (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE 0 e hh k) := by
  let R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf
  let f := nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE 0 e hh k
  let : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) :=
    nativeProjectiveModulePresheafMap_isLocallySurjective 𝓑 𝒟 ℰ hD hE e hh hpre k
  let : Epi ((SheafOfModules.toSheaf R).map f) := inferInstance
  exact (SheafOfModules.toSheaf R).epi_of_epi_map inferInstance

end LinearStudy
