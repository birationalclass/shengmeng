module
public import Linear.GradedSurjectiveNativeCharts
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open HomogeneousLocalization HomogeneousIdeal AlgebraicGeometry CategoryTheory
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem graded_surjective_irrelevant_le_map (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) : irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  apply (irrelevant_le ℬ).mpr
  intro j hj b hb
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_lift f hf j b hb
  exact Ideal.mem_map_of_mem f (mem_irrelevant_of_mem 𝒜 hj ha)

theorem projective_surjective_comap_image_zeroLocus (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (s : Set B) :
    (ProjectiveSpectrum.comap f (graded_surjective_irrelevant_le_map f hf)) ''
      ProjectiveSpectrum.zeroLocus ℬ s =
    ProjectiveSpectrum.zeroLocus 𝒜 (f ⁻¹' s ∪ (RingHom.ker f.toRingHom : Set A)) := by
  classical
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩ a ha
    rcases ha with ha | ha
    · exact hq ha
    · change f a ∈ q.asHomogeneousIdeal
      rw [show f a=0 from ha]
      exact q.asHomogeneousIdeal.zero_mem
  · intro hp
    have hker : RingHom.ker f.toRingHom ≤ p.asHomogeneousIdeal.toIdeal :=
      fun a ha => hp (Or.inr ha)
    let q : ProjectiveSpectrum ℬ :=
      ⟨p.asHomogeneousIdeal.map f,Ideal.map_isPrime_of_surjective hf hker,by
        intro h
        apply p.not_irrelevant_le
        apply (irrelevant_le 𝒜).mpr
        intro j hj a ha
        have hfa := h (mem_irrelevant_of_mem ℬ hj (Graded.map_mem f ha))
        change a ∈ (p.asHomogeneousIdeal.toIdeal.map f).comap f at hfa
        rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot] at hfa
        change a ∈ p.asHomogeneousIdeal.toIdeal ⊔ RingHom.ker f.toRingHom at hfa
        rw [sup_eq_left.mpr hker] at hfa
        exact hfa⟩
    refine ⟨q,?_,?_⟩
    · intro b hb
      obtain ⟨a,rfl⟩ := hf b
      exact Ideal.mem_map_of_mem f (hp (Or.inl hb))
    · apply ProjectiveSpectrum.ext
      apply HomogeneousIdeal.ext
      exact (Ideal.comap_map_of_surjective f hf _).trans
        (by
          rw [← RingHom.ker_eq_comap_bot]
          change p.asHomogeneousIdeal.toIdeal ⊔ RingHom.ker f.toRingHom = _
          exact sup_eq_left.mpr hker)

theorem projective_surjective_comap_closedEmbedding (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding
      (ProjectiveSpectrum.comap f (graded_surjective_irrelevant_le_map f hf)) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (ProjectiveSpectrum.comap f _).continuous
  · intro p q hpq
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    apply Ideal.comap_injective_of_surjective f hf
    exact congrArg (fun x : ProjectiveSpectrum 𝒜 => x.asHomogeneousIdeal.toIdeal) hpq
  · intro s hs
    obtain ⟨t,rfl⟩ := (ProjectiveSpectrum.isClosed_iff_zeroLocus ℬ s).mp hs
    rw [projective_surjective_comap_image_zeroLocus f hf]
    exact ProjectiveSpectrum.isClosed_zeroLocus 𝒜 _

/-- The actual homogeneous local-ring map of a surjective graded map
is surjective. Numerator and denominator are lifted in the same degree. -/
theorem graded_surjective_native_localRingHom (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (J : Ideal B) [J.IsPrime] :
    Function.Surjective (localRingHom f (J.comap f) J rfl) := by
  intro b
  obtain ⟨⟨j,bnum,bden,hden⟩,rfl⟩ := mk_surjective b
  obtain ⟨anum,hanum,hnum⟩ := graded_surjective_homogeneous_lift f hf j bnum.val bnum.property
  obtain ⟨aden,haden,hdeneq⟩ := graded_surjective_homogeneous_lift f hf j bden.val bden.property
  let c : NumDenSameDeg 𝒜 (J.comap f).primeCompl :=
    ⟨j,⟨anum,hanum⟩,⟨aden,haden⟩,by
      change f aden ∉ J
      rwa [hdeneq]⟩
  refine ⟨mk c,?_⟩
  rw [localRingHom,map_mk]
  apply congrArg mk
  dsimp [c]
  congr 1 <;> apply Subtype.ext
  · exact hnum
  · exact hdeneq

/-- A surjective graded map induces the genuine native Proj closed
immersion, proved by closed embedding on points and surjectivity on
the native scheme stalks. -/
theorem graded_surjective_Proj_map_closedImmersion (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (graded_surjective_irrelevant_le_map f hf)) where
  isClosedEmbedding := projective_surjective_comap_closedEmbedding f hf
  stalkMap_surjective p := by
    change Function.Surjective
      ((Proj.sheafedSpaceMap f (graded_surjective_irrelevant_le_map f hf)).hom.stalkMap p).hom
    rw [← Proj.localRingHom_comp_stalkIso]
    change Function.Surjective
      ((Proj.stalkIso ℬ p).inv.hom.comp
        ((localRingHom f _ _ rfl).comp
          (Proj.stalkIso 𝒜 (ProjectiveSpectrum.comap f _ p)).hom.hom))
    exact (ConcreteCategory.bijective_of_isIso (Proj.stalkIso ℬ p).inv).2.comp
      ((graded_surjective_native_localRingHom f hf p.asHomogeneousIdeal.toIdeal).comp
        (ConcreteCategory.bijective_of_isIso
          (Proj.stalkIso 𝒜 (ProjectiveSpectrum.comap f _ p)).hom).2)

end LinearStudy
