module
public import Linear.SchemeModuleHomOpenScalars
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

theorem schemeModulesRestrictFunctor_map_add {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (h k : M ⟶ N) :
    (Scheme.Modules.restrictFunctor f).map (h + k) =
      (Scheme.Modules.restrictFunctor f).map h + (Scheme.Modules.restrictFunctor f).map k := by
  apply SheafOfModules.hom_ext
  ext W x
  rfl

variable {X : Scheme.{u}} (M N : X.Modules)
theorem schemeModuleHomAffineChartSectionsEquiv_direct_add
    (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R)
    (h k : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomAffineChartSectionsEquiv M N U R e (h + k) =
      schemeModuleHomAffineChartSectionsEquiv M N U R e h +
      schemeModuleHomAffineChartSectionsEquiv M N U R e k := by
  simp only [schemeModuleHomAffineChartSectionsEquiv, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv, Iso.homCongr_apply, Equiv.coe_fn_mk]
  rw [schemeModuleHomOpenSectionsEquiv_add]
  rw [schemeModulesRestrictFunctor_map_add]
  simp only [Preadditive.comp_add,Preadditive.add_comp]

end LinearStudy
