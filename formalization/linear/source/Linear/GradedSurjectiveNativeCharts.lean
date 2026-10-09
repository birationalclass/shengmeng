module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open HomogeneousLocalization
variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A surjective graded homomorphism lifts a homogeneous element in its
same degree. The lift is the degree component of an arbitrary preimage. -/
theorem graded_surjective_homogeneous_lift (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (j : ℕ) (b : B) (hb : b ∈ ℬ j) :
    ∃ a : A,a ∈ 𝒜 j ∧ f a=b := by
  obtain ⟨a,ha⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a j,(DirectSum.decompose 𝒜 a j).property,?_⟩
  rw [f.map_directSumDecompose,ha]
  simp only [DirectSum.decompose_of_mem ℬ hb, DirectSum.of_eq_same]

/-- Surjectivity of the actual map of homogeneous native chart rings.
No reducedness, integrality or field assumption is needed. -/
theorem graded_surjective_native_away_map (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (j : ℕ) (s : A) (hs : s ∈ 𝒜 j) :
    Function.Surjective (Away.map f s) := by
  intro b
  obtain ⟨m,a,ha,rfl⟩ := Away.mk_surjective ℬ (Graded.map_mem f hs) b
  obtain ⟨v,hv,hva⟩ := graded_surjective_homogeneous_lift f hf (m • j) a ha
  refine ⟨Away.mk 𝒜 hs m v hv,?_⟩
  rw [Away.map_mk]
  subst a
  rfl

end LinearStudy
