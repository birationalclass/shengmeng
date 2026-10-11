module
public import Linear.SchemeModuleHomOpenImmersionIso
public import Linear.AffineFinitePresentationInternalHomQuasicoherent
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
variable {X : Scheme.{u}} {R : CommRingCat.{u}}
variable (M N : X.Modules) (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- The ORIGINAL global Hom sheaf restricted to an affine chart is
quasicoherent if the same source and target restrict quasicoherently
and the actual source global-section module is finitely presented.
No target Hom quasicoherence or comparison certificate is assumed. -/
theorem schemeModuleHomAffineRestriction_isQuasicoherent
    [(M.restrict j).IsQuasicoherent] [(N.restrict j).IsQuasicoherent]
    [Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj (M.restrict j))] :
    ((schemeModuleHomModuleSheaf M N).restrict j).IsQuasicoherent := by
  haveI := affineFinitePresentationInternalHom_isQuasicoherent (M.restrict j) (N.restrict j)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (schemeModuleHomOpenImmersionIso M N j).symm inferInstance
end LinearStudy
