module
public import Linear.SchemeModuleHomGluing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Actual internal-Hom module sections, with the original restriction maps,
glue uniquely on an actual open cover. The gluing premise is ordinary pairwise
restriction equality, to be discharged by the native symmetric overlap proof. -/
theorem schemeModuleHomSections_existsUnique_gluing {ι : Type*}
    (U : ι → X.Opens) (V : X.Opens) (iUV : ∀ i, U i ⟶ V)
    (hcover : V ≤ iSup U)
    (sigma : ∀ i, Γ(schemeModuleHomModuleSheaf M N,U i))
    (hc : ∀ i j,
      (schemeModuleHomModuleSheaf M N).presheaf.map (infLELeft (U i) (U j)).op (sigma i) =
      (schemeModuleHomModuleSheaf M N).presheaf.map (infLERight (U i) (U j)).op (sigma j)) :
    ∃! s : Γ(schemeModuleHomModuleSheaf M N,V),
      ∀ i, (schemeModuleHomModuleSheaf M N).presheaf.map (iUV i).op s = sigma i := by
  let f := fun i => schemeModuleHomModuleSectionsEquiv M N (U i) (sigma i)
  have hf : ∀ i j, schemeModuleHomRestrict M N (infLELeft (U i) (U j)) (f i) =
      schemeModuleHomRestrict M N (infLERight (U i) (U j)) (f j) := by
    intro i j
    exact (schemeModuleHomModuleSectionsEquiv_restrict M N (infLELeft (U i) (U j)) (sigma i)).symm.trans
      ((congrArg (schemeModuleHomModuleSectionsEquiv M N (U i ⊓ U j)) (hc i j)).trans
        (schemeModuleHomModuleSectionsEquiv_restrict M N (infLERight (U i) (U j)) (sigma j)))
  obtain ⟨g,hg,hu⟩ := schemeModuleHom_existsUnique_gluing M N U V iUV hcover f hf
  refine ⟨(schemeModuleHomModuleSectionsEquiv M N V).symm g, ?_, ?_⟩
  · intro i
    apply (schemeModuleHomModuleSectionsEquiv M N (U i)).injective
    simpa only [Equiv.apply_symm_apply] using
      (schemeModuleHomModuleSectionsEquiv_restrict M N (iUV i)
        ((schemeModuleHomModuleSectionsEquiv M N V).symm g)).trans (hg i)
  · intro s hs
    apply (schemeModuleHomModuleSectionsEquiv M N V).injective
    rw [Equiv.apply_symm_apply]
    apply hu
    intro i
    exact (schemeModuleHomModuleSectionsEquiv_restrict M N (iUV i) s).symm.trans
      (congrArg (schemeModuleHomModuleSectionsEquiv M N (U i)) (hs i))

/-- Restriction equality on an original open equal to U intersect V is
exactly the standard overlap compatibility. Open equality is the only
transport; the actual restriction maps and sections are unchanged. -/
theorem schemeModuleSections_infRestrictionEq_of_originalEqualOpen
    (G : X.Modules) (U V W : X.Opens) (h : W = U ⊓ V)
    (hl : W ≤ U) (hr : W ≤ V) (s : Γ(G,U)) (t : Γ(G,V))
    (he : G.presheaf.map (homOfLE hl).op s = G.presheaf.map (homOfLE hr).op t) :
    G.presheaf.map (infLELeft U V).op s = G.presheaf.map (infLERight U V).op t := by
  subst W
  exact he
end LinearStudy
