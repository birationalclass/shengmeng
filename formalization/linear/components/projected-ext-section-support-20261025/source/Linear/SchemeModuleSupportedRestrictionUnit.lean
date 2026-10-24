module
public import Linear.SchemeModuleIsoOnActualCover
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- Vanishing of an ACTUAL original module sheaf implies vanishing of
its ACTUAL section group on every original open. -/
theorem schemeModule_sections_isZero_of_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : IsZero M) (W : X.Opens) : IsZero Γ(M,W) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := congrArg (fun f : M ⟶ M => f.app W) (hM.eq_of_src (𝟙 M) 0)
  simpa only [Scheme.Modules.Hom.id_app,Scheme.Modules.Hom.zero_app] using h

/-- Vanishing after an ACTUAL original open restriction implies zero
ACTUAL sections on every original subopen of its image. -/
theorem schemeModule_sections_isZero_of_openRestriction {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules)
    (hM : IsZero ((Scheme.Modules.restrictFunctor j).obj M))
    (W : Y.Opens) (hW : W ≤ j ''ᵁ ⊤) : IsZero Γ(M,W) := by
  have he : j ''ᵁ (j ⁻¹ᵁ W) = W :=
    (j.image_preimage_eq_opensRange_inf W).trans
      (inf_eq_right.mpr (hW.trans (le_of_eq j.image_top_eq_opensRange)))
  have hz := schemeModule_sections_isZero_of_isZero
    ((Scheme.Modules.restrictFunctor j).obj M) hM (j ⁻¹ᵁ W)
  change IsZero Γ(M,j ''ᵁ (j ⁻¹ᵁ W)) at hz
  exact Eq.mp (congrArg (fun V : Y.Opens => IsZero Γ(M,V)) he) hz

/-- The ACTUAL native adjunction unit becomes an isomorphism on the
SAME actual main open,using mathlib's fully faithful original pushforward. -/
theorem schemeModule_restrictionUnit_restrict_isIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.restrictAdjunction j).unit.app M)) := by
  infer_instance

/-- If the SAME actual module sheaf has zero sections on all subopens
of V,its ACTUAL restriction-adjunction unit is an isomorphism on each
such subopen. Both source and target groups are proved zero. -/
theorem schemeModule_restrictionUnit_app_isIso_of_zero_sections {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules) (V : Y.Opens)
    (hz : ∀ W : Y.Opens,W ≤ V → IsZero Γ(M,W))
    (W : Y.Opens) (hW : W ≤ V) :
    IsIso (((Scheme.Modules.restrictAdjunction j).unit.app M).app W) := by
  have hsrc := hz W hW
  have htgt : IsZero Γ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.restrictFunctor j).obj M),W) := by
    change IsZero Γ(M,j ''ᵁ (j ⁻¹ᵁ W))
    exact hz _ ((j.image_preimage_le W).trans hW)
  exact isIso_of_source_target_iso_zero _ hsrc.isoZero htgt.isoZero

/-- Glue the ACTUAL native restriction-adjunction unit over the ORIGINAL
main open and ORIGINAL supplementary opens. The cover and zero sections
are EXPLICIT generic hypotheses;the Koszul application derives them. -/
theorem schemeModule_restrictionUnit_isIso_of_originalCover {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules) {ι : Type*}
    (V : ι → Y.Opens)
    (hc : ∀ y : Y,y ∈ j ''ᵁ ⊤ ∨ ∃ i,y ∈ V i)
    (hz : ∀ i W,W ≤ V i → IsZero Γ(M,W)) :
    IsIso ((Scheme.Modules.restrictAdjunction j).unit.app M) := by
  let U : Option ι → Y.Opens := fun t =>
    match t with | none => j ''ᵁ ⊤ | some i => V i
  have hcover : (⊤ : Y.Opens) ≤ iSup U := by
    intro y _
    rcases hc y with hmain | ⟨i,hi⟩
    · exact Opens.mem_iSup.mpr ⟨none,hmain⟩
    · exact Opens.mem_iSup.mpr ⟨some i,hi⟩
  apply schemeModuleMorphism_isIso_of_originalCover U hcover
  intro t W hW
  cases t with
  | none =>
    letI := schemeModule_restrictionUnit_restrict_isIso j M
    exact schemeModuleMorphism_app_isIso_of_openImmersion
      ((Scheme.Modules.restrictAdjunction j).unit.app M) j W hW
  | some i =>
    exact schemeModule_restrictionUnit_app_isIso_of_zero_sections j M (V i) (hz i) W hW

end LinearStudy
