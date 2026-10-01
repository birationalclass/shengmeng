module

public import Negativity.CodimensionOne
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- A dense open section of a separated morphism identifies the morphism
over that open. This version does not require a reduced image scheme. -/
theorem isIso_over_dense_open_section {Z X : Scheme.{u}} (π : Z ⟶ X)
    [IsSeparated π] (U : X.Opens) (t : U.toScheme ⟶ Z)
    [IsOpenImmersion t] [IsDominant t] (ht : t ≫ π = U.ι) :
    IsIso (π ∣_ U) := by
  have hrange : Set.range t ⊆ Set.range (π ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change π (t x) ∈ U
    rw [← Scheme.Hom.comp_apply, ht]
    exact x.2
  let s : U.toScheme ⟶ (π ⁻¹ᵁ U) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι t hrange
  have hs : s ≫ (π ⁻¹ᵁ U).ι = t := IsOpenImmersion.lift_fac _ _ hrange
  have : IsOpenImmersion (s ≫ (π ⁻¹ᵁ U).ι) := by rw [hs]; infer_instance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s (π ⁻¹ᵁ U).ι
  have : IsDominant (s ≫ (π ⁻¹ᵁ U).ι) := by rw [hs]; infer_instance
  have : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s (π ⁻¹ᵁ U).ι
  have hsection : s ≫ (π ∣_ U) = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hs, ht, Category.id_comp]
  have : IsClosedImmersion (s ≫ (π ∣_ U)) := by rw [hsection]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (π ∣_ U)
  have : Surjective s := surjective_of_isDominant_of_isClosed_range s
    s.isClosedEmbedding.isClosed_range
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsIso (s ≫ (π ∣_ U)) := by rw [hsection]; infer_instance
  exact IsIso.of_isIso_comp_left s (π ∣_ U)

/-- The scheme-theoretic graph closure used in Hartshorne's Chow construction.
Given a map from a nonempty open into a proper S-scheme P, we construct the
actual closure Z inside X ×[S] P. Its projections are proper, and Z → X is
birational. This does not yet construct the finite family of projective
embeddings or the finite normalization required by the full Chow lemma. -/
theorem hartshorne_graph_closure {X S P : Scheme.{u}} [IsIntegral X]
    [NoetherianSpace X] (f : X ⟶ S) [IsProper f] (p : P ⟶ S) [IsProper p]
    (U : X.Opens) (hU : Nonempty U) (g : U.toScheme ⟶ P)
    (hg : g ≫ p = U.ι ≫ f) :
    ∃ (Z : Scheme.{u}) (π : Z ⟶ X) (q : Z ⟶ P) (t : U.toScheme ⟶ Z),
      IsProper π ∧ IsProper q ∧ π ≫ f = q ≫ p ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ π = U.ι ∧
      BirationalMorphism π ∧ Surjective π := by
  let graph : U.toScheme ⟶ pullback f p := pullback.lift U.ι g hg.symm
  have : NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact graph := inferInstance
  have hgraph : graph ≫ pullback.fst f p = U.ι := by simp [graph]
  have : IsImmersion (graph ≫ pullback.fst f p) := by rw [hgraph]; infer_instance
  have : IsImmersion graph := IsImmersion.of_comp graph (pullback.fst f p)
  let π : graph.image ⟶ X := graph.imageι ≫ pullback.fst f p
  let q : graph.image ⟶ P := graph.imageι ≫ pullback.snd f p
  have : IsProper π := by dsimp [π]; infer_instance
  have : IsProper q := by dsimp [q]; infer_instance
  have ht : graph.toImage ≫ π = U.ι := by simp [π, hgraph]
  have : IsIso (π ∣_ U) := isIso_over_dense_open_section π U graph.toImage ht
  have hbir : BirationalMorphism π := ⟨U, hU, inferInstance⟩
  refine ⟨graph.image, π, q, graph.toImage, inferInstance, inferInstance,
    ?_, inferInstance, inferInstance, ht, hbir, proper_birational_surjective π hbir⟩
  dsimp [π, q]
  simp only [Category.assoc, pullback.condition]

end Negativity
