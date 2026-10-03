module

public import Negativity.HartshorneGraph
public import Negativity.CurveImageGeometry
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A graph immersion whose first coordinate is determined by one
immersion into a target coordinate has an immersive second projection. -/
theorem actual_graph_projection_isImmersion
    {Z X S P T : Scheme.{u}} (f : X ⟶ S) (p : P ⟶ S)
    (b : T ⟶ S) (a : P ⟶ T) (j : X ⟶ T) [IsImmersion j]
    (ha : a ≫ b = p) (hj : j ≫ b = f)
    (π : Z ⟶ X) (q : Z ⟶ P) (hw : π ≫ f = q ≫ p)
    [IsImmersion (pullback.lift π q hw)] (he : π ≫ j = q ≫ a) :
    IsImmersion q := by
  let r : Z ⟶ pullback j a := pullback.lift π q he
  let v : pullback j a ⟶ pullback f p := pullback.lift
    (pullback.fst j a) (pullback.snd j a) (by
      rw [← hj, ← ha, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hr : r ≫ v = pullback.lift π q hw := by
    apply pullback.hom_ext <;> simp [r, v]
  have : IsImmersion (r ≫ v) := by rw [hr]; infer_instance
  have : IsImmersion r := IsImmersion.of_comp r v
  rw [← show r ≫ pullback.snd j a = q by simp [r]]
  infer_instance

/-- Final theorem: Hartshorne's actual graph closure has finite second
projection once the actual source is covered by opens immersing into
the corresponding proper target coordinates. Dense graph identities
are extended on the reduced image, not assumed on the whole closure.
The target coordinate family and its common rational map are genuine
geometric data; their finite projective-product construction remains a
separate part of Chow's lemma. -/
theorem hartshorne_graph_second_projection_finite
    {X S P : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (f : X ⟶ S) [IsProper f] (p : P ⟶ S) [IsProper p]
    {ι : Type*} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (T : ι → Scheme.{u}) (b : ∀ i, T i ⟶ S)
    (hb : ∀ i, IsSeparated (b i))
    (a : ∀ i, P ⟶ T i) (ha : ∀ i, a i ≫ b i = p)
    (j : ∀ i, (U i).toScheme ⟶ T i) (hj : ∀ i, IsImmersion (j i))
    (hbase : ∀ i, j i ≫ b i = (U i).ι ≫ f)
    (W : X.Opens) (hW : Nonempty W) (hWU : ∀ i, W ≤ U i)
    (g : W.toScheme ⟶ P) (hg : g ≫ p = W.ι ≫ f)
    (hcoord : ∀ i, g ≫ a i = X.homOfLE (hWU i) ≫ j i) :
    ∃ (Z : Scheme.{u}) (π : Z ⟶ X) (q : Z ⟶ P),
      IsProper π ∧ BirationalMorphism π ∧ Surjective π ∧
      IsIntegral Z ∧ IsFinite q ∧ π ≫ f = q ≫ p := by
  let graph : W.toScheme ⟶ pullback f p := pullback.lift W.ι g hg.symm
  have : NoetherianSpace W.toScheme := W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact graph := inferInstance
  have hgraph : graph ≫ pullback.fst f p = W.ι := by simp [graph]
  have : IsImmersion (graph ≫ pullback.fst f p) := by rw [hgraph]; infer_instance
  have : IsImmersion graph := IsImmersion.of_comp graph (pullback.fst f p)
  let Z := graph.image
  let π : Z ⟶ X := graph.imageι ≫ pullback.fst f p
  let q : Z ⟶ P := graph.imageι ≫ pullback.snd f p
  let t : W.toScheme ⟶ Z := graph.toImage
  have : IsProper π := by dsimp [π]; infer_instance
  have : IsProper q := by dsimp [q]; infer_instance
  have : IsReduced Z := actual_image_isReduced graph
  have : IsOpenImmersion t := inferInstance
  have : IsDominant t := inferInstance
  have hr : IsPreirreducible (Set.range t) := by
    simpa using (PreirreducibleSpace.isPreirreducible_univ (X := W.toScheme)).image
      t t.continuous.continuousOn
  have : IrreducibleSpace Z := {
    isPreirreducible_univ := by rw [← t.denseRange.closure_range]; exact hr.closure
    toNonempty := ⟨t hW.some⟩ }
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced _
  have ht : t ≫ π = W.ι := by simp [t, π, hgraph]
  have htq : t ≫ q = g := by simp [t, q, graph]
  have hw : π ≫ f = q ≫ p := by dsimp [π, q]; simp [pullback.condition]
  have : IsIso (π ∣_ W) := isIso_over_dense_open_section π W t ht
  have hbir : BirationalMorphism π := ⟨W, hW, inferInstance⟩
  have hlocal (i : ι) : IsImmersion ((π ⁻¹ᵁ U i).ι ≫ q) := by
    let V := π ⁻¹ᵁ U i
    let s : W.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι t (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change π (t x) ∈ U i
      rw [← Scheme.Hom.comp_apply, ht]
      exact hWU i x.2)
    have hs : s ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
    have : IsDominant (s ≫ V.ι) := by rw [hs]; infer_instance
    have : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s V.ι
    have hsp : s ≫ (π ∣_ U i) = X.homOfLE (hWU i) := by
      rw [← cancel_mono (U i).ι, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, hs, ht, Scheme.homOfLE_ι]
    have : IsSeparated (b i) := hb i
    have : IsImmersion (j i) := hj i
    have he : (π ∣_ U i) ≫ j i = V.ι ≫ q ≫ a i := by
      apply ext_of_isDominant_of_isSeparated (b i) ?_ s ?_
      · simp only [Category.assoc, hbase, ha]
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hw]
      · rw [← Category.assoc, hsp, ← hcoord]
        rw [← Category.assoc s V.ι, hs, ← Category.assoc, htq]
    have hv : (π ∣_ U i) ≫ ((U i).ι ≫ f) = (V.ι ≫ q) ≫ p := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hw, Category.assoc]
      rfl
    let v : V.toScheme ⟶ pullback ((U i).ι ≫ f) p :=
      pullback.lift (π ∣_ U i) (V.ι ≫ q) hv
    let c : pullback ((U i).ι ≫ f) p ⟶ pullback f p :=
      pullback.map _ _ _ _ (U i).ι (𝟙 P) (𝟙 S) (by simp) (by simp)
    have hc : v ≫ c = V.ι ≫ graph.imageι := by
      apply pullback.hom_ext <;> simp [v, c, π, q, V]
    have : IsImmersion (v ≫ c) := by rw [hc]; infer_instance
    have : IsImmersion v := IsImmersion.of_comp v c
    exact actual_graph_projection_isImmersion ((U i).ι ≫ f) p (b i) (a i) (j i)
      (ha i) (hbase i) (π ∣_ U i) (V.ι ≫ q) hv he
  have : LocallyQuasiFinite q := by
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite)
      (fun i => π ⁻¹ᵁ U i) (by rw [← Scheme.Hom.preimage_iSup, hcover]; simp)
    intro i
    have := hlocal i
    infer_instance
  have : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  exact ⟨Z, π, q, inferInstance, hbir, proper_birational_surjective π hbir,
    inferInstance, inferInstance, hw⟩

end
end Negativity
