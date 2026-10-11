module
public import Linear.AffineQuasicoherentSourceMorphisms
public import Linear.SchemeModuleHomTopSections
public import Linear.SchemeModuleHomEvaluationRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {R : CommRingCat.{u}} (M N : (Spec R).Modules)
variable [M.IsQuasicoherent]

/-- Actual internal Hom sections on an affine scheme are precisely
linear maps of the SAME global sections when the source is quasicoherent.
The target is an arbitrary module sheaf. -/
def affineQuasicoherentHomGlobalSectionsEquiv :
    Γ(schemeModuleHomModuleSheaf M N,⊤) ≃
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj N) :=
  (schemeModuleHomTopSectionsEquiv M N).trans
    ((affineQuasicoherentSourceMorphismsEquiv M N).trans
      (ModuleCat.homEquiv
        (M := (moduleSpecΓFunctor (R := R)).obj M)
        (N := (moduleSpecΓFunctor (R := R)).obj N)))

/-- The equivalence is genuine evaluation of the original Hom section,
not an independently chosen identification of the same carriers. -/
theorem affineQuasicoherentHomGlobalSectionsEquiv_evaluation
    (h : Γ(schemeModuleHomModuleSheaf M N,⊤)) (x : Γ(M,⊤)) :
    affineQuasicoherentHomGlobalSectionsEquiv M N h x =
      schemeModuleHomSectionEvaluation M N ⊤ h x := by
  rw [affineQuasicoherentHomGlobalSectionsEquiv, Equiv.trans_apply,
    Equiv.trans_apply, affineQuasicoherentSourceMorphismsEquiv_apply]
  rfl

/-- The same actual evaluation equivalence preserves the original affine
scalar action, for finite-presentation localization of the Hom module. -/
def affineQuasicoherentHomGlobalSectionsLinearEquiv :
    Γ(schemeModuleHomModuleSheaf M N,⊤) ≃ₗ[R]
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj N) := by
  let E := affineQuasicoherentHomGlobalSectionsEquiv M N
  refine { __ := E, map_add' := ?_, map_smul' := ?_ }
  · intro h k
    ext x
    simp only [affineQuasicoherentHomGlobalSectionsEquiv_evaluation,
      LinearMap.add_apply]
    rfl
  · intro c h
    ext x
    simp only [affineQuasicoherentHomGlobalSectionsEquiv_evaluation,
      LinearMap.smul_apply]
    rfl
end LinearStudy
