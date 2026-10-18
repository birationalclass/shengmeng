module
public import Linear.AffineQuasicoherentSourceMorphisms
public import Linear.SchemeModuleHomAffineChartSections
public import Linear.SchemeModuleHomOpenScalars
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : CommRingCat.{u}} (M N : (Spec R).Modules)
variable [M.IsQuasicoherent]

/-- On EVERY open U of the original affine scheme, genuine Hom sections
are linear maps from the SAME global source sections into the actual
sections of the open-target pushforward. Source quasicoherence suffices;
the open need not be principal or affine. This uses the existing actual
restriction/pushforward adjunction and tilde adjunction. -/
def affineQuasicoherentHomOpenSectionsEquiv (U : (Spec R).Opens) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι))) :=
  (schemeModuleHomOpenSectionsEquiv M N U).trans
    (((Scheme.Modules.restrictAdjunction U.ι).homEquiv M (N.restrict U.ι)).trans
      ((affineQuasicoherentSourceMorphismsEquiv M
        ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι))).trans
          (ModuleCat.homEquiv
            (M := (moduleSpecΓFunctor (R := R)).obj M)
            (N := (moduleSpecΓFunctor (R := R)).obj
              ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι))))))

/-- The open Hom equivalence is the real restriction unit followed by
the original local morphism. No extension or evaluation agreement is
assumed. -/
theorem affineQuasicoherentHomOpenSectionsEquiv_evaluation
    (U : (Spec R).Opens) (h : Γ(schemeModuleHomModuleSheaf M N,U))
    (x : Γ(M,⊤)) :
    affineQuasicoherentHomOpenSectionsEquiv M N U h x =
      ((Scheme.Modules.pushforward U.ι).map
        (schemeModuleHomOpenSectionsEquiv M N U h)).app ⊤
          (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app ⊤ x) := by
  rw [affineQuasicoherentHomOpenSectionsEquiv, Equiv.trans_apply,
    Equiv.trans_apply, Equiv.trans_apply,
    affineQuasicoherentSourceMorphismsEquiv_apply, Adjunction.homEquiv_apply]
  rfl

/-- The same actual open-section equivalence preserves the original
R-scalar action, for codomain localization on principal opens. -/
def affineQuasicoherentHomOpenSectionsLinearEquiv (U : (Spec R).Opens) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃ₗ[R]
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι))) := by
  let E := affineQuasicoherentHomOpenSectionsEquiv M N U
  refine { __ := E, map_add' := ?_, map_smul' := ?_ }
  · intro h k
    ext x
    simp only [LinearMap.add_apply]
    rfl
  · intro c h
    ext x
    change affineQuasicoherentHomOpenSectionsEquiv M N U (c • h) x =
      c • affineQuasicoherentHomOpenSectionsEquiv M N U h x
    rw [Scheme.Modules.smul_Spec_def (M := schemeModuleHomModuleSheaf M N)]
    simp only [affineQuasicoherentHomOpenSectionsEquiv_evaluation,
      schemeModuleHomOpenSectionsEquiv_smul, Functor.map_comp,
      Scheme.Modules.Hom.comp_app, ModuleCat.comp_apply,
      Scheme.Modules.pushforward_map_app, originalGlobalModuleScalar_app]
    rfl

end LinearStudy
