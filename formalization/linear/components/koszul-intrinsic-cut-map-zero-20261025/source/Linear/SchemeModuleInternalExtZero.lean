module
public import Linear.SchemeModuleDerivedInternalHom
public import Linear.SchemeModuleInternalHomCoefficientLimits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL zero derived SHEAF Ext is ACTUAL original internal Hom.
Left exactness has been proved from native original sections,not supplied. -/
def schemeModuleInternalExtZeroIso (P : X.Modules) :
    schemeModuleInternalExtFunctor P 0 ≅ schemeModuleInternalHomCoefficientFunctor X P := by
  letI := schemeModuleInternalHomCoefficientFunctor_preservesFiniteLimits X P
  exact (schemeModuleInternalHomCoefficientFunctor X P).rightDerivedZeroIsoSelf

/-- Retain the SAME actual coefficient morphism under zero-degree comparison. -/
theorem schemeModuleInternalExtZeroIso_naturality (P : X.Modules)
    {M N : X.Modules} (c : M ⟶ N) :
    (schemeModuleInternalExtFunctor P 0).map c ≫
        ((schemeModuleInternalExtZeroIso P).app N).hom =
      ((schemeModuleInternalExtZeroIso P).app M).hom ≫ schemeModuleHomPostcompose c :=
  (schemeModuleInternalExtZeroIso P).hom.naturality c

/-- The inverse is the NATIVE map to the zero right derived functor. -/
theorem schemeModuleInternalExtZeroIso_inv_app (P N : X.Modules) :
    ((schemeModuleInternalExtZeroIso P).app N).inv =
      (schemeModuleInternalHomCoefficientFunctor X P).toRightDerivedZero.app N := rfl

/-- Sections of ACTUAL zero SHEAF Ext on each ORIGINAL open are actual
local module-sheaf morphisms,not a separate Hom model. -/
def schemeModuleInternalExtZeroSectionEquiv (P N : X.Modules) (U : X.Opens) :
    Γ(schemeModuleInternalExt P N 0,U) ≃ (P.over U ⟶ N.over U) :=
  (((SheafOfModules.evaluation X.ringCatSheaf (op U)) ⋙
      forget (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U)))).mapIso
        ((schemeModuleInternalExtZeroIso P).app N)).toEquiv.trans
          (schemeModuleHomModuleSectionsEquiv P N U)

end LinearStudy
