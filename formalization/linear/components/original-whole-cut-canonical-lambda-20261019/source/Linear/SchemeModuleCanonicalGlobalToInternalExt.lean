module
public import Linear.SchemeModuleGlobalToInternalExtNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- ACTUAL positive global-to-local Ext map,using the native chosen
injective resolution. Independence of that choice has been PROVED. -/
def schemeModuleGlobalToInternalExt (P N : X.Modules) (n : ℕ) :
    Ext.{u} P N (n+1) →+
      (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N (n+1)) :=
  schemeModuleGlobalToInternalExtViaResolution (injectiveResolution N) P n

/-- Compute the SAME map by ANY actual coefficient injective resolution. -/
theorem schemeModuleGlobalToInternalExt_eq_viaResolution (P N : X.Modules) (n : ℕ)
    (I : InjectiveResolution N) :
    schemeModuleGlobalToInternalExt P N n = schemeModuleGlobalToInternalExtViaResolution I P n :=
  schemeModuleGlobalToInternalExtViaResolution_independent (injectiveResolution N) I P n

/-- Coefficient naturality for the constructed ACTUAL global-to-local map. -/
theorem schemeModuleGlobalToInternalExt_naturality (P : X.Modules)
    {M N : X.Modules} (c : M ⟶ N) (n : ℕ) (e : Ext.{u} P M (n+1)) :
    schemeModuleGlobalToInternalExt P N n (e.comp (Ext.mk₀ c) (add_zero _)) =
      schemeModuleGlobalToInternalExt P M n e ≫
        (schemeModuleInternalExtFunctor P (n+1)).map c := by
  let I := injectiveResolution M
  let J := injectiveResolution N
  let phi : InjectiveResolution.Hom I J c :=
    { hom := InjectiveResolution.desc c J I
      ι_f_zero_comp_hom_f_zero := by
        simpa using InjectiveResolution.desc_commutes_zero c J I }
  exact schemeModuleGlobalToInternalExtViaResolution_naturality I J P phi n e

/-- SAME canonical map into ACTUAL sections of the derived internal Ext
sheaf over the whole ORIGINAL scheme. It is not asserted to be an isomorphism. -/
def schemeModuleGlobalToInternalExtSections (P N : X.Modules) (n : ℕ) :
    Ext.{u} P N (n+1) →+ Γ(schemeModuleInternalExt P N (n+1),⊤) :=
  schemeModuleGlobalToInternalExtSectionsViaResolution (injectiveResolution N) P n

end LinearStudy
