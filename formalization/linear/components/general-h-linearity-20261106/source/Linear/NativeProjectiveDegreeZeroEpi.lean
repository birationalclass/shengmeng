module
public import Linear.NativeProjectiveDegreeZeroMap
public import Linear.NativeProjectiveModuleFractionLift
public import Linear.IntegerGradedSurjectionPreimage
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
variable [DirectSum.Decomposition 𝒟] [DirectSum.Decomposition ℰ]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → b • x ∈ ℰ ((n : ℤ) + d))
variable (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → e x ∈ ℰ d)
include hh

/-- Ordinary homogeneous surjectivity gives local section lifts for the
same-twist actual native presheaf map. Numerator preimages are derived
from the original integer decompositions. -/
theorem nativeProjectiveDegreeZeroPresheafMap_isLocallySurjective
    (he : Function.Surjective e) (k : ℤ) :
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝓑))
      (nativeProjectiveDegreeZeroPresheafMap 𝓑 𝒟 ℰ hD hE e hh k) := by
  have hpre := integerDegreeZeroSurjection_homogeneous_preimages 𝒟 ℰ e hh he
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U f p hp
  let ff : nativeProjectiveModuleSections 𝓑 ℰ hE k (op U) := f
  have hf := ff.property
  change (nativeProjectiveModuleLocalPredicate 𝓑 ℰ k).pred ff.1 at hf
  obtain ⟨V, hpV, i, hfrac⟩ := hf ⟨p, hp⟩
  obtain ⟨g, hg, heq⟩ := nativeProjectiveModuleFraction_lifts 𝓑 𝒟 ℰ e hpre k hfrac
  have hglocal : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred g :=
    fun q => ⟨V, q.property, 𝟙 V, hg⟩
  let s : nativeProjectiveModuleSections 𝓑 𝒟 hD k (op V) := ⟨g, hglocal⟩
  refine ⟨V, i.le, ⟨s, ?_⟩, hpV⟩
  apply Subtype.ext
  funext q
  exact heq q

/-- Actual degree-zero surjections induce native sheaf epimorphisms,
using the SAME twist on both sides. -/
theorem nativeProjectiveDegreeZeroSheafMap_epi (he : Function.Surjective e) (k : ℤ) :
    Epi (nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k) := by
  let R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf
  let f := nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k
  let : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) :=
    nativeProjectiveDegreeZeroPresheafMap_isLocallySurjective 𝓑 𝒟 ℰ hD hE e hh he k
  let : Epi ((SheafOfModules.toSheaf R).map f) := inferInstance
  exact (SheafOfModules.toSheaf R).epi_of_epi_map inferInstance

end LinearStudy
