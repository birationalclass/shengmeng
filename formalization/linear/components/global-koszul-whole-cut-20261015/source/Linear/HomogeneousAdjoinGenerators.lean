module
public import Linear.GradedSubalgebraDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Lift the actual finite generating set into the algebra it adjoins. -/
def adjoinLiftedGenerators (s : Finset A) : Finset (Algebra.adjoin K (s : Set A)) :=
  s.attach.map
    ⟨fun a : {a : A // a ∈ s} => ⟨a.val, Algebra.subset_adjoin a.property⟩,
      fun a b h => Subtype.ext
        (congrArg (fun z : Algebra.adjoin K (s : Set A) => (z : A)) h)⟩

theorem adjoinLiftedGenerators_card (s : Finset A) :
    (adjoinLiftedGenerators (K := K) s).card = s.card := by
  simp [adjoinLiftedGenerators]

/-- The lifted generators generate the ACTUAL subalgebra, not an abstract replacement. -/
theorem adjoinLiftedGenerators_generate (s : Finset A) :
    Algebra.adjoin K (adjoinLiftedGenerators (K := K) s : Set (Algebra.adjoin K (s : Set A))) = ⊤ := by
  let B := Algebra.adjoin K (s : Set A)
  let C := Algebra.adjoin K (adjoinLiftedGenerators (K := K) s : Set B)
  have hB : B ≤ C.map B.val := by
    apply Algebra.adjoin_le
    intro a ha
    let b : B := ⟨a, Algebra.subset_adjoin ha⟩
    have hb : b ∈ adjoinLiftedGenerators (K := K) s :=
      Finset.mem_map.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩
    exact ⟨b, Algebra.subset_adjoin hb, rfl⟩
  apply le_antisymm le_top
  intro b hb
  change b ∈ C
  obtain ⟨c, hc, heq⟩ := hB b.property
  have hcb : c = b := Subtype.ext heq
  rw [← hcb]
  exact hc

theorem adjoinLiftedGenerators_homogeneous (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    (s : Finset A) (d : ℕ) (hs : ∀ a ∈ s, a ∈ 𝒜 d) :
    ∀ b ∈ adjoinLiftedGenerators (K := K) s,
      b ∈ gradedSubalgebraPiece 𝒜 (Algebra.adjoin K (s : Set A)) d := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  exact hs a.val a.property

end LinearStudy
