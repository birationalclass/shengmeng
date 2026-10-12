module
public import Linear.SchemeModuleHomAffineChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g]

/-- Actual unit-module transport through the composition is exactly
the two genuine structure-sheaf pullbacks, on every original chart open. -/
theorem structureModuleCompositeChartValue (W : X.Opens)
    (r : Γ(Z,g ''ᵁ (f ''ᵁ W))) :
    let N : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
    ((Scheme.Modules.restrictUnitIso (f ≫ g)).hom).app W
      (((Scheme.Modules.restrictFunctorComp f g).symm.app N).hom.app W
        (((N.restrict g).restrictAppIso f W).inv
          ((N.restrictAppIso g (f ''ᵁ W)).inv r))) =
    (f.appIso W).hom ((g.appIso (f ''ᵁ W)).hom r) := by
  dsimp only
  change ((f ≫ g).appIso W).hom
      (Z.presheaf.map (eqToHom (by simp)).op r) =
    (f.appIso W).hom ((g.appIso (f ''ᵁ W)).hom r)
  rw [Scheme.Hom.comp_appIso]
  dsimp only [Iso.trans_hom]
  simp only [ConcreteCategory.comp_apply, Functor.mapIso_hom]
  congr 2
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp

end LinearStudy
