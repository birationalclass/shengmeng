module
public import Linear.SheafEmbeddingSectionTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- Conditional transport of a fixed positive-twist embedding.
The native embedding is an EXPLICIT input, to be supplied by the previously
proved original finite-normalization construction. The still-unverified
canonical identification is also explicit. This general transport theorem
does not construct or identify a genuine dualizing complex.

The SAME m is chosen before F and its identification; in particular this
transport introduces no dependence on an iterate. The concrete large-type
original-Proj specialization has not passed its new compilation and must
not be represented as a completed original Lemma4.1. -/
theorem moduleSheaf_exists_fixed_positive_twist_mono_under_identification
    {X : Scheme.{u}} (D : X.Modules) (T : ℕ → X.Modules)
    (nativeEmbedding : ∃ m : ℕ, 0 < m ∧ ∃ j : D ⟶ T m,
      Mono j ∧ (T m).IsLocallyFree ∧ (T m).IsQuasicoherent) :
    ∃ m : ℕ, 0 < m ∧ ∀ (F : X.Modules) (canonicalIdentification : F ≅ D),
      ∃ j : F ⟶ T m, Mono j ∧ (T m).IsLocallyFree ∧ (T m).IsQuasicoherent := by
  obtain ⟨m,hm,nativeMap,hmono,hfree,hqc⟩ := nativeEmbedding
  letI : Mono nativeMap := hmono
  exact ⟨m,hm,fun F canonicalIdentification =>
    ⟨canonicalIdentification.hom ≫ nativeMap, inferInstance, hfree, hqc⟩⟩

/-- The downstream section step in original Lemma4.2, for the SAME fixed
embedding. A nonzero section gives a nonzero image section, and its
vanishing on every actual pulled-back subscheme is preserved. This is
not a proof of the preceding proper/Koszul duality or polynomial extension. -/
theorem moduleSheafMono_nonzero_section_with_pullback_vanishing
    {X : Scheme.{u}} {F T G : X.Modules} (j : F ⟶ T) [Mono j]
    (s : G ⟶ F) (hs : s ≠ 0) {I : Type u}
    (Z : I → Scheme.{u}) (i : ∀ a, Z a ⟶ X)
    (hvanish : ∀ a, (Scheme.Modules.pullback (i a)).map s = 0) :
    ∃ t : G ⟶ T, t = s ≫ j ∧ t ≠ 0 ∧
      ∀ a, (Scheme.Modules.pullback (i a)).map t = 0 := by
  exact ⟨s ≫ j,rfl,moduleSheafMono_postcompose_ne_zero j s hs,
    fun a => moduleSheafMap_pullback_vanishing (i a) j s (hvanish a)⟩
end LinearStudy
