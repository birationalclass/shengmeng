module
public import Linear.OriginalGlobalModuleScalar
public import Linear.SchemeModuleFiniteSupportCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
/-- The actual abelian-sheaf coefficient map still acts on original
sections by the ORIGINAL global scalar restricted to the same open. -/
theorem schemeModuleActualAbelianScalar_app {X : Scheme.{u}}
    (r : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) (x : Γ(M,U)) :
    (((schemeModuleToActualAbelianSheaf X).map (originalGlobalModuleScalar r M)).hom.app (op U)) x =
      X.presheaf.map U.leTop.op r • x :=
  originalGlobalModuleScalar_app r M U x
end LinearStudy
