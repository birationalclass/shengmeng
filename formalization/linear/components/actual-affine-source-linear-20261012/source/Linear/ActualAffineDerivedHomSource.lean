module
public import Linear.ActualAffineNativeDualSourceLinear
public import Linear.NativeDerivedCoextensionZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- H^0 of every actual coextended injective resolution is the actual
affine internal Hom, as a B-module with the original source action.
This is an affine derived calculation, not a dualizing-identification axiom. -/
def actualAffineCoextendedInjectiveResolutionOriginalHomZeroIso
    (I : InjectiveResolution (ModuleCat.of A A)) :
    let H := Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)
    letI : Module B H := actualAffineOriginalHomSourceModule (A := A) (B := B)
    (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) 0).obj
      (((ModuleCat.coextendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) ≅ ModuleCat.of B H := by
  dsimp only
  let H := Γ(schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
    (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)
  letI : Module B H := actualAffineOriginalHomSourceModule (A := A) (B := B)
  exact nativeCoextendedInjectiveResolutionHomologyZeroIso
    (algebraMap A B) (ModuleCat.of A A) I ≪≫
    (actualAffineNativeDualOriginalHomSourceLinearEquiv (A := A) (B := B)).toModuleIso

end LinearStudy
