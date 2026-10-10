module
public import Linear.SchemeModuleHomAffineChartSections
public import Linear.OriginalGlobalModuleScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The actual internal Hom section comparison on the SAME original open
preserves its actual scalar action after transport to the open scheme. -/
theorem schemeModuleHomOpenSectionsEquiv_smul (U : X.Opens)
    (r : Γ(X,U)) (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomOpenSectionsEquiv M N U (r • h) =
      schemeModuleHomOpenSectionsEquiv M N U h ≫
        originalGlobalModuleScalar (U.topIso.inv r) (N.restrict U.ι) := by
  apply SheafOfModules.hom_ext
  ext W x
  let V : Over U := U.overEquivalence.inverse.obj W.unop
  change (show Γ(X,V.left) from X.presheaf.map V.hom.op r) •
      (show Γ(N,V.left) from h.val.app (op V) x) =
    (show Γ(X,V.left) from (U.ι.appIso W.unop).inv
      ((U : Scheme).presheaf.map W.unop.leTop.op (U.topIso.inv r))) •
      (show Γ(N,V.left) from h.val.app (op V) x)
  congr 1
  apply (ConcreteCategory.bijective_of_isIso (U.ι.appIso W.unop).hom).injective
  dsimp only
  rw [Iso.inv_hom_id_apply]
  have he : X.presheaf.map V.hom.op ≫ (U.ι.appIso W.unop).hom =
      U.topIso.inv ≫ (U : Scheme).presheaf.map W.unop.leTop.op := by
    rw [Scheme.Opens.ι_appIso]
    change X.presheaf.map V.hom.op ≫ 𝟙 _ =
      X.presheaf.map (eqToHom U.ι_image_top).op ≫
        X.presheaf.map (U.ι.opensFunctor.map W.unop.leTop).op
    rw [Category.comp_id, ← X.presheaf.map_comp]
    congr 1
  exact congr($(he) r)

theorem schemeModuleHomOpenSectionsEquiv_add (U : X.Opens)
    (h k : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomOpenSectionsEquiv M N U (h + k) =
      schemeModuleHomOpenSectionsEquiv M N U h +
        schemeModuleHomOpenSectionsEquiv M N U k := by
  apply SheafOfModules.hom_ext
  ext W x
  rfl

end LinearStudy
