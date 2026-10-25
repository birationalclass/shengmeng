module
public import Linear.SchemeModuleHomPrecompose
public import Linear.SchemeModuleHomAffineChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {M' M N : X.Modules}
/-- The actual Hom section comparison retains precomposition by the
genuine restricted source module morphism. No source-action compatibility is assumed. -/
theorem schemeModuleHomOpenSectionsEquiv_precompose (u : M' ⟶ M) (U : X.Opens)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomOpenSectionsEquiv M' N U ((schemeModuleHomPrecompose u).app U h) =
      (Scheme.Modules.restrictFunctor U.ι).map u ≫
        schemeModuleHomOpenSectionsEquiv M N U h := by
  change (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app M')
      ((Scheme.Modules.overFunctorEquiv U).app N))
    ((Scheme.Modules.overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map u ≫
        (schemeModuleHomModuleSectionsEquiv M N U h))) = _
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk, schemeModuleHomOpenSectionsEquiv,
    Equiv.trans_apply, Functor.FullyFaithful.homEquiv]
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.app]
  have hn := (Scheme.Modules.overFunctorEquiv U).inv.naturality u
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
end LinearStudy
