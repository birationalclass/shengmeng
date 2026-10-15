module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace TopologicalSpace.Opens Opposite
universe u
variable {X Y : Scheme.{u}} {M N : X.Modules}

/-- A morphism of actual module sheaves is an isomorphism if its
section maps on every subopen of an actual open cover are isomorphisms.
The proof reuses mathlib's sheaf isomorphism criterion on a basis. -/
theorem schemeModuleMorphism_isIso_of_originalCover {ι : Type*}
    (U : ι → X.Opens) (hcover : (⊤ : X.Opens) ≤ iSup U)
    (f : M ⟶ N) (hl : ∀ i W, W ≤ U i → IsIso (f.app W)) : IsIso f := by
  let B := fun W : {W : X.Opens // ∃ i, W ≤ U i} => W.val
  have hb : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    have hxc : x ∈ iSup U := hcover (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
    refine ⟨V ⊓ U i, ⟨⟨V ⊓ U i, i, inf_le_right⟩, rfl⟩, ?_, inf_le_left⟩
    exact ⟨hx,hi⟩
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf,M.isSheaf⟩
  let G : TopCat.Sheaf Ab X := ⟨N.presheaf,N.isSheaf⟩
  let g : F ⟶ G := ⟨f.mapPresheaf⟩
  have hg : IsIso g := TopCat.Sheaf.isIso_iff_isIso_basis hb (fun W => by
    obtain ⟨i,hi⟩ := W.property
    exact hl i W.val hi)
  have hn : IsIso f.mapPresheaf := by
    exact (show IsIso ((TopCat.Sheaf.forget Ab X).map g) from inferInstance)
  exact (isIso_iff_of_reflects_iso f (Scheme.Modules.toPresheaf X)).mp hn

/-- An actual isomorphism after restriction along an open immersion
is an isomorphism on sections of each original subopen of its image. -/
theorem schemeModuleMorphism_app_isIso_of_openImmersion
    (f : M ⟶ N) (j : Y ⟶ X) [IsOpenImmersion j]
    [IsIso ((Scheme.Modules.restrictFunctor j).map f)]
    (U : X.Opens) (hU : U ≤ j ''ᵁ ⊤) : IsIso (f.app U) := by
  have he : j ''ᵁ (j ⁻¹ᵁ U) = U :=
    (j.image_preimage_eq_opensRange_inf U).trans
      (inf_eq_right.mpr (hU.trans (le_of_eq j.image_top_eq_opensRange)))
  have hf : IsIso (((Scheme.Modules.restrictFunctor j).map f).app (j ⁻¹ᵁ U)) := inferInstance
  change IsIso (f.app (j ''ᵁ (j ⁻¹ᵁ U))) at hf
  exact Eq.mp (congrArg (fun V : X.Opens => IsIso (f.app V)) he) hf
end LinearStudy
