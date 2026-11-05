module
public import Linear.NoetherianInjectiveStructureSheafSections
public import Linear.SchemeModuleFlasqueExtAcyclic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Abelian Opposite
universe u
/-- The actual sheaf associated to an injective R-module is flasque on Noetherian Spec R.
Injectivity in the category of ALL module sheaves is not assumed or asserted. -/
theorem noetherian_injective_tilde_isFlasque (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : ModuleCat.{u} R) [Module.Injective R I] :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf (Spec R)).obj (tilde I)) := by
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  change Function.Surjective ((structureSheafInType R I).obj.map i)
  intro s
  obtain ⟨x,hx⟩ := noetherian_injective_structureSheaf_toOpen_surjective V.unop s
  refine ⟨StructureSheaf.toOpenₗ R I U.unop x,?_⟩
  change StructureSheaf.toOpenₗ R I V.unop x = s
  exact hx

/-- Images of actual injective R-modules are acyclic for GLOBAL structure-unit Ext on Spec R. -/
theorem noetherian_injective_tilde_globalUnitExt_vanish
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : ModuleCat.{u} R) [Module.Injective R I] (n : ℕ) :
    Subsingleton (Ext.{u} (SheafOfModules.unit (Spec R).ringCatSheaf) (tilde I) (n+1)) :=
  schemeModule_flasque_relativeExt_vanish (Spec R) (tilde I)
    (noetherian_injective_tilde_isFlasque R I) n
end LinearStudy