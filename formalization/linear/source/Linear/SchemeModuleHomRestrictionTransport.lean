module
public import Linear.SchemeModuleScalarRestriction
public import Linear.SchemeModuleHomOpenScalars
public import Linear.SchemeModuleScalarNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (f : Y ⟶ (U : Scheme)) [IsOpenImmersion f]
variable {P Q : Y.Modules}

/-- The ORIGINAL open Hom comparison, actually restricted along f,
then conjugated by the given actual module isomorphisms. -/
def schemeModuleHomRestrictionTransport
    (α : (M.restrict U.ι).restrict f ≅ P)
    (β : (N.restrict U.ι).restrict f ≅ Q)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) : P ⟶ Q :=
  α.inv ≫ (Scheme.Modules.restrictFunctor f).map
    (schemeModuleHomOpenSectionsEquiv (X := X) M N U h) ≫ β.hom

/-- Actual restriction and actual O-linear isomorphisms preserve the
SAME original Hom scalar. No scalar-comparison hypothesis is supplied. -/
theorem schemeModuleHomRestrictionTransport_smul
    (α : (M.restrict U.ι).restrict f ≅ P)
    (β : (N.restrict U.ι).restrict f ≅ Q)
    (r : Γ(X,U)) (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomRestrictionTransport M N U f α β (r • h) =
      schemeModuleHomRestrictionTransport M N U f α β h ≫
        originalGlobalModuleScalar (X := Y) (f.appTop (U.topIso.inv r)) Q := by
  unfold schemeModuleHomRestrictionTransport
  rw [schemeModuleHomOpenSectionsEquiv_smul, Functor.map_comp]
  rw [originalGlobalModuleScalar_restrict]
  have hn := originalGlobalModuleScalar_naturality (X := Y)
    (f.appTop (U.topIso.inv r)) β.hom
  simpa only [Category.assoc] using congrArg
    (fun z => α.inv ≫ (Scheme.Modules.restrictFunctor f).map
      (schemeModuleHomOpenSectionsEquiv (X := X) M N U h) ≫ z) hn

theorem schemeModuleHomRestrictionTransport_add
    (α : (M.restrict U.ι).restrict f ≅ P)
    (β : (N.restrict U.ι).restrict f ≅ Q)
    (h k : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomRestrictionTransport M N U f α β (h + k) =
      schemeModuleHomRestrictionTransport M N U f α β h +
        schemeModuleHomRestrictionTransport M N U f α β k := by
  have hl : (Scheme.Modules.restrictFunctor f).map
      (schemeModuleHomOpenSectionsEquiv M N U (h + k)) =
    (Scheme.Modules.restrictFunctor f).map (schemeModuleHomOpenSectionsEquiv M N U h) +
      (Scheme.Modules.restrictFunctor f).map (schemeModuleHomOpenSectionsEquiv M N U k) := by
    rw [schemeModuleHomOpenSectionsEquiv_add]
    apply SheafOfModules.hom_ext
    ext W x
    rfl
  unfold schemeModuleHomRestrictionTransport
  rw [hl]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

end LinearStudy
