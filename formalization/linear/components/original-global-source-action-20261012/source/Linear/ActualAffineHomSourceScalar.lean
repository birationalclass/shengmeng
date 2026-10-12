module
public import Linear.ActualAffineNativeDualSourceLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
theorem actualAffineOriginalHomSourceModule_smul
    (b : B) (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)) :
    letI := actualAffineOriginalHomSourceModule (A := A) (B := B)
    b • h = schemePushforwardHomSourceActionSection
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) h := rfl
end LinearStudy
