module
public import Linear.SchemeModuleSupportedRestrictionUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Compose GENERICALLY the SAME actual native adjunction-unit iso with
the pushforward of a PROVIDED original chart iso. Both input conditions
are explicit;original applications construct them. -/
def schemeModuleSupportedRestrictionIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules) (Q : X.Modules)
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app M))
    (e : (Scheme.Modules.restrictFunctor j).obj M ≅ Q) :
    M ≅ (Scheme.Modules.pushforward j).obj Q := by
  letI := hu
  exact asIso ((Scheme.Modules.restrictAdjunction j).unit.app M) ≪≫
    (Scheme.Modules.pushforward j).mapIso e

/-- The comparison uses the SAME original unit and SAME original chart
map,so its hom is the actual canonical composite. -/
theorem schemeModuleSupportedRestrictionIso_hom {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules) (Q : X.Modules)
    (hu : IsIso ((Scheme.Modules.restrictAdjunction j).unit.app M))
    (e : (Scheme.Modules.restrictFunctor j).obj M ≅ Q) :
    (schemeModuleSupportedRestrictionIso j M Q hu e).hom =
      (Scheme.Modules.restrictAdjunction j).unit.app M ≫
        (Scheme.Modules.pushforward j).map e.hom := rfl

end LinearStudy
