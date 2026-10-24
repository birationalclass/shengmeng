module
public import Linear.DiscreteSchemeProjectorImageSupport
public import Linear.DiscreteSchemePointProjectedExtDecomposition
public import Linear.SchemeModuleSupportedRestrictionUnit
public import Linear.SchemeModuleGlobalToInternalExtSourceNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- For an ACTUAL source morphism vanishing on an actual open,the SAME
canonical internal-Ext section of EVERY pulled-back global class vanishes
there. Factor through its actual image and reuse original source naturality;
no replacement Ext class,comparison map or coefficient is supplied. -/
theorem schemeModuleGlobalToInternalExtSections_precompose_restrict_zero
    {X : Scheme.{u}} {A B W : X.Modules} (b : A ⟶ B) (V : X.Opens)
    (hb : (Scheme.Modules.restrictFunctor V.ι).map b=0)
    (n : ℕ) (z : Ext.{u} B W (n+1)) :
    (schemeModuleInternalExt A W (n+1)).presheaf.map V.leTop.op
      (schemeModuleGlobalToInternalExtSections A W n
        ((Ext.mk₀ b).comp z (zero_add _)))=0 := by
  let I := Abelian.image b
  let i : I ⟶ B := Abelian.image.ι b
  let p : A ⟶ I := Abelian.factorThruImage b
  let w : Ext.{u} I W (n+1) := (Ext.mk₀ i).comp z (zero_add _)
  have hfactor : (Ext.mk₀ p).comp w (zero_add _)=(Ext.mk₀ b).comp z (zero_add _) := by
    dsimp [w,p,i]
    rw [Ext.mk₀_comp_mk₀_assoc,Abelian.image.fac]
  have hI : IsZero ((schemeModuleInternalExt I W (n+1)).restrict V.ι) :=
    schemeModuleInternalExt_open_isZero_of_source V.ι I W
      (schemeModuleImage_open_isZero_of_map_zero b V hb) (n+1)
  have hs := schemeModule_sections_isZero_of_openRestriction V.ι
    (schemeModuleInternalExt I W (n+1)) hI V (le_of_eq V.ι_image_top.symm)
  letI := AddCommGrpCat.subsingleton_of_isZero hs
  rw [← hfactor,schemeModuleGlobalToInternalExtSections_sourceNaturality]
  let g := schemeModuleInternalExtSourceMap p W (n+1)
  have hnat := (ConcreteCategory.congr_hom (g.mapPresheaf.naturality V.leTop.op)
    (schemeModuleGlobalToInternalExtSections I W n w)).symm
  change (schemeModuleInternalExt A W (n+1)).presheaf.map V.leTop.op
    (g.app ⊤ (schemeModuleGlobalToInternalExtSections I W n w))=
      g.app V ((schemeModuleInternalExt I W (n+1)).presheaf.map V.leTop.op
        (schemeModuleGlobalToInternalExtSections I W n w)) at hnat
  rw [show (schemeModuleInternalExt I W (n+1)).presheaf.map V.leTop.op
    (schemeModuleGlobalToInternalExtSections I W n w)=0 from Subsingleton.elim _ _,map_zero] at hnat
  exact hnat
/-- The SAME actual projected class has zero canonical INTERNAL-SHEAF-Ext
section on EVERY actual open whose inverse image avoids its chosen component.
The source restriction identity is derived from the constructed projector. -/
theorem discreteSchemeProjectedExtClass_internal_section_restrict_zero
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (L : D.Modules)
    (U : D.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ V ≤ (show D.Opens from ⟨(U : Set D)ᶜ,isOpen_discrete _⟩))
    (W : X.Modules) (n : ℕ)
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W (n+1)) :
    (schemeModuleInternalExt ((Scheme.Modules.pushforward f).obj L) W (n+1)).presheaf.map V.leTop.op
      (schemeModuleGlobalToInternalExtSections ((Scheme.Modules.pushforward f).obj L) W n
        (discreteSchemeProjectedExtClass f L U z))=0 :=
  schemeModuleGlobalToInternalExtSections_precompose_restrict_zero _ V
    (discreteSchemePushforwardOpenProjector_restrict_zero f L U V h) n z
/-- ACTUAL point support of the SAME canonical internal-Ext section:it
vanishes on every original open avoiding f(x),without finite source or
closed-immersion hypotheses. Nonzero point trace weights remain separate. -/
theorem discreteSchemePointProjectedExtClass_internal_section_vanish_away
    {D X : Scheme.{u}} [DiscreteTopology D] (f : D ⟶ X) (L : D.Modules)
    (x : D) (V : X.Opens) (hx : f x ∉ V) (W : X.Modules) (n : ℕ)
    (z : Ext.{u} ((Scheme.Modules.pushforward f).obj L) W (n+1)) :
    (schemeModuleInternalExt ((Scheme.Modules.pushforward f).obj L) W (n+1)).presheaf.map V.leTop.op
      (schemeModuleGlobalToInternalExtSections ((Scheme.Modules.pushforward f).obj L) W n
        (discreteSchemePointProjectedExtClass f L x z))=0 := by
  apply discreteSchemeProjectedExtClass_internal_section_restrict_zero f L (discreteSchemePointOpen D x) V ?_ W n z
  intro y hy
  change y ≠ x
  intro heq
  subst y
  exact hx hy
end LinearStudy
