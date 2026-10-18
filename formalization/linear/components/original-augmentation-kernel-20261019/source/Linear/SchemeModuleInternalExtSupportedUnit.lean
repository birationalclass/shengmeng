module
public import Linear.SchemeModuleInternalExtOpenSupport
public import Linear.SchemeModuleSupportedRestrictionUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
/-- The SAME original ambient cover and ACTUAL source vanishing on its
supplementary opens DERIVE the actual restriction-adjunction unit iso
for derived SHEAF Ext,ALL coefficients and ALL degrees. No Ext-support
or gluing certificate is assumed. Original Koszul geometry supplies the
cover and source vanishings independently of this generic theorem. -/
theorem schemeModuleInternalExt_restrictionUnit_isIso_of_originalCover
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (P N : X.Modules) (q : ℕ) {ι : Type*} (V : ι → X.Opens)
    (hc : ∀ x : X,x ∈ j ''ᵁ ⊤ ∨ ∃ i,x ∈ V i)
    (hP : ∀ i,IsZero (P.restrict (V i).ι)) :
    IsIso ((Scheme.Modules.restrictAdjunction j).unit.app (schemeModuleInternalExt P N q)) := by
  apply schemeModule_restrictionUnit_isIso_of_originalCover j (schemeModuleInternalExt P N q) V hc
  intro i W hW
  exact schemeModule_sections_isZero_of_openRestriction (V i).ι (schemeModuleInternalExt P N q)
    (schemeModuleInternalExt_open_isZero_of_source (V i).ι P N (hP i) q) W
    (hW.trans (le_of_eq (V i).ι_image_top.symm))
/-- If the ACTUAL target unit is an isomorphism,actual open restriction
detects vanishing of EVERY original morphism into it. This is a proved
adjunction criterion;the preceding source-support theorem constructs the
unit iso for the actual internal Ext targets. -/
theorem schemeModule_morphism_zero_iff_restrict_of_target_unit_isIso
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {A B : X.Modules} (a : A ⟶ B)
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app B)) :
    a = 0 ↔ (Scheme.Modules.restrictFunctor j).map a = 0 := by
  letI := hu
  constructor
  · intro hz
    rw [hz,Functor.map_zero]
  · intro hz
    apply (cancel_mono ((Scheme.Modules.restrictAdjunction j).unit.app B)).mp
    have h := (Scheme.Modules.restrictAdjunction j).unit.naturality a
    change a ≫ (Scheme.Modules.restrictAdjunction j).unit.app B =
      (Scheme.Modules.restrictAdjunction j).unit.app A ≫
        (Scheme.Modules.pushforward j).map ((Scheme.Modules.restrictFunctor j).map a) at h
    rw [h,hz,Functor.map_zero,comp_zero,zero_comp]
end LinearStudy
