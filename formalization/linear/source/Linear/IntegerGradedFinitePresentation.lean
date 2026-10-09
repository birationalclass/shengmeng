module
public import Linear.IntegerGradedFiniteRelations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open Classical
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
include hD

/-- Construct an ACTUAL degree-preserving finite free presentation.
Both free modules, generator degrees and maps are constructed, and
image of the actual relation map equals the actual generator-map kernel. -/
theorem integerGradedFinite_exists_shiftedFree_presentation
    [IsNoetherianRing S] [Module.Finite S M] :
    ∃ s : Finset M,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
        Function.Surjective e ∧
          (∀ d : ℤ, ∀ f : s → S, f ∈ integerShiftedFreePiece 𝓑 w d → e f ∈ 𝒟 d) ∧
          ∃ t : Finset e.ker,
            letI := Classical.decEq t
            ∃ z : t → ℤ,
              let a := integerShiftedFreeGeneratorMap (S := S)
                (fun i : t => ((i : e.ker) : s → S))
              LinearMap.range a = e.ker ∧
                ∀ d : ℤ, ∀ f : t → S, f ∈ integerShiftedFreePiece 𝓑 z d →
                  a f ∈ integerShiftedFreePiece 𝓑 w d := by
  classical
  obtain ⟨s, w, he, hh, t, ht, hthom⟩ :=
    integerGradedFinite_exists_shiftedFree_homogeneous_relations 𝓑 𝒟 hD
  let e := integerShiftedFreeGeneratorMap (S := S) (fun i : s => (i : M))
  let z : t → ℤ := fun i => Classical.choose (hthom i i.property)
  have hz : ∀ i : t, ((i : e.ker) : s → S) ∈ integerShiftedFreePiece 𝓑 w (z i) :=
    fun i => Classical.choose_spec (hthom i i.property)
  let a := integerShiftedFreeGeneratorMap (S := S)
    (fun i : t => ((i : e.ker) : s → S))
  let a0 := integerShiftedFreeGeneratorMap (S := S) (fun i : t => (i : e.ker))
  have hrange : Set.range (fun i : t => (i : e.ker)) = (t : Set e.ker) := by
    ext x
    simp
  have hgen : Submodule.span S (Set.range (fun i : t => (i : e.ker))) = ⊤ := by
    rw [hrange]
    exact ht
  have ha0 : Function.Surjective a0 := integerShiftedFreeGeneratorMap_surjective _ hgen
  have ha : a = e.ker.subtype.comp a0 := by
    apply LinearMap.ext
    intro f
    change (∑ i : t, f i • ((i : e.ker) : s → S)) =
      ((∑ i : t, f i • (i : e.ker) : e.ker) : s → S)
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hex : LinearMap.range a = e.ker := by
    rw [ha, LinearMap.range_comp, LinearMap.range_eq_top.mpr ha0,
      Submodule.map_top, Submodule.range_subtype]
  exact ⟨s, w, he, hh, t, z, hex,
    integerShiftedFreeGeneratorMap_homogeneous 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) z _ hz⟩

end LinearStudy
