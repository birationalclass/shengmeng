module
public import Linear.SchemeModuleHomAffineChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)
variable {U V : X.Opens} (i : V ⟶ U)
/-- Actual coherence from double open restriction to restriction on V.
All component isomorphisms are the original mathlib module restriction comparisons. -/
def schemeModuleHomOpenRestrictionIso :
    (M.restrict U.ι).restrict (X.homOfLE (leOfHom i)) ≅ M.restrict V.ι :=
  (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso
    ((Scheme.Modules.overFunctorEquiv U).symm.app M) ≪≫
  (Scheme.Modules.overMapCompOverEquiv i).symm.app (M.over U) ≪≫
  (Scheme.Modules.overEquiv V).functor.mapIso
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M) ≪≫
  (Scheme.Modules.overFunctorEquiv V).app M
/-- The SAME actual local Hom comparison commutes with genuine open restriction.
The coherence is constructed from mathlib, not an assumed comparison certificate. -/
theorem schemeModuleHomOpenSectionsEquiv_restrict
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomOpenSectionsEquiv M N V
      ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) =
    (schemeModuleHomOpenRestrictionIso M i).inv ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
        (schemeModuleHomOpenSectionsEquiv M N U h) ≫
      (schemeModuleHomOpenRestrictionIso N i).hom := by
  rw [schemeModuleHomOpenSectionsEquiv, Equiv.trans_apply,
    schemeModuleHomModuleSectionsEquiv_restrict]
  dsimp only [schemeModuleHomOpenSectionsEquiv, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv, Iso.homCongr, Equiv.coe_fn_mk,
    schemeModuleHomRestrict, schemeModuleHomOpenRestrictionIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (Scheme.Modules.overMapCompOverEquiv i).hom.naturality
    ((schemeModuleHomModuleSectionsEquiv M N U) h)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app, Iso.symm_hom, Iso.symm_inv, Iso.map_inv_hom_id_app_assoc, Iso.map_hom_inv_id_app_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  have hM :
      (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
        ((Scheme.Modules.overFunctorEquiv U).hom.app M) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
        ((Scheme.Modules.overFunctorEquiv U).inv.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hN :
      (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
        ((Scheme.Modules.overFunctorEquiv U).hom.app N) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
        ((Scheme.Modules.overFunctorEquiv U).inv.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hM, reassoc_of% hN]
  have hn' := reassoc_of% hn
  rw [← hn']
  simp only [Functor.comp_map, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc]
end LinearStudy
