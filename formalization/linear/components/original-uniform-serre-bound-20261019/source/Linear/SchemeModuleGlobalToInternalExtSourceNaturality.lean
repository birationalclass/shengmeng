module
public import Linear.SchemeModuleCocycleToInternalExtSourceNaturality
public import Linear.SchemeModuleCanonicalGlobalToInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- Descend actual source naturality through the PROVED native cocycle presentation. -/
theorem schemeModuleGlobalToInternalExtViaResolution_sourceNaturality
    {P Q N : X.Modules} (I : InjectiveResolution N) (g : P ⟶ Q)
    (n : ℕ) (e : Ext.{u} Q N (n+1)) :
    schemeModuleGlobalToInternalExtViaResolution I P n ((Ext.mk₀ g).comp e (zero_add _)) =
      schemeModuleGlobalToInternalExtViaResolution I Q n e ≫
        schemeModuleInternalExtSourceMap g N (n+1) := by
  obtain ⟨f,rfl⟩ := injectiveCocycleExtMap_surjective I Q (n+1) e
  rw [injectiveCocycleExtMap_precompose]
  rw [schemeModuleGlobalToInternalExtViaResolution_cocycle,
    schemeModuleGlobalToInternalExtViaResolution_cocycle]
  exact schemeModuleInjectiveCocycleToInternalExt_sourceNaturality I g (n+1) f

/-- The existing canonical global-to-local Ext map is source-natural. -/
theorem schemeModuleGlobalToInternalExt_sourceNaturality
    {P Q N : X.Modules} (g : P ⟶ Q) (n : ℕ) (e : Ext.{u} Q N (n+1)) :
    schemeModuleGlobalToInternalExt P N n ((Ext.mk₀ g).comp e (zero_add _)) =
      schemeModuleGlobalToInternalExt Q N n e ≫
        schemeModuleInternalExtSourceMap g N (n+1) :=
  schemeModuleGlobalToInternalExtViaResolution_sourceNaturality (injectiveResolution N) g n e

/-- Source naturality on ACTUAL global sections of the SAME internal Ext sheaf. -/
theorem schemeModuleGlobalToInternalExtSections_sourceNaturality
    {P Q N : X.Modules} (g : P ⟶ Q) (n : ℕ) (e : Ext.{u} Q N (n+1)) :
    schemeModuleGlobalToInternalExtSections P N n ((Ext.mk₀ g).comp e (zero_add _)) =
      (schemeModuleInternalExtSourceMap g N (n+1)).app ⊤
        (schemeModuleGlobalToInternalExtSections Q N n e) := by
  exact congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N (n+1) =>
      f.val.app (Opposite.op ⊤) (1 : Γ(X,⊤)))
    (schemeModuleGlobalToInternalExt_sourceNaturality g n e)

end LinearStudy
