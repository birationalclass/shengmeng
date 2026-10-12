module
public import Linear.StructureUnitMapValue
public import Linear.SchemeIsoTopPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
theorem structureUnitChartTopValue {X T : Scheme.{u}} (U : X.Opens)
    (e : ↑U ≅ T) (r : Γ(X,U)) :
    HEq ((Scheme.Modules.restrictUnitIso (e.inv ≫ U.ι)).hom.app ⊤
      (X.presheaf.map (eqToHom (show (e.inv ≫ U.ι) ''ᵁ ⊤ = U by simp)).op r))
      (e.inv.appTop (U.topIso.inv r)) := by
  apply heq_of_eq
  change ((e.inv ≫ U.ι).appIso ⊤).hom (X.presheaf.map _ r) = _
  rw [Scheme.Hom.comp_appIso]
  dsimp only [Iso.trans_hom]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply, Functor.mapIso_hom]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  apply ConcreteCategory.congr_hom
  erw [schemeIsoAppIsoTopHom e.symm]
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map,
    ← Category.assoc, ← Functor.map_comp]
  simp only [Category.comp_id, ← CategoryTheory.Functor.map_comp]
  congr 1
end LinearStudy
