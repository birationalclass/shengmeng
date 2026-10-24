module
public import Linear.SchemeModuleScalarNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
/-- Original coefficient multiplication by zero is the zero morphism. -/
theorem originalGlobalModuleScalar_zero (M : X.Modules) :
    originalGlobalModuleScalar 0 M = 0 := by
  apply SheafOfModules.hom_ext
  ext U x
  change X.presheaf.map U.unop.leTop.op 0 • x = 0
  simp
/-- Original coefficient multiplication by one is the identity morphism. -/
theorem originalGlobalModuleScalar_one (M : X.Modules) :
    originalGlobalModuleScalar 1 M = 𝟙 M := by
  apply SheafOfModules.hom_ext
  ext U x
  change X.presheaf.map U.unop.leTop.op 1 • x = x
  simp
/-- The original scalar endomorphism is additive in the original global section. -/
theorem originalGlobalModuleScalar_add (r s : Γ(X,⊤)) (M : X.Modules) :
    originalGlobalModuleScalar (r+s) M =
      originalGlobalModuleScalar r M + originalGlobalModuleScalar s M := by
  apply SheafOfModules.hom_ext
  ext U x
  change X.presheaf.map U.unop.leTop.op (r+s) • x =
    X.presheaf.map U.unop.leTop.op r • x + X.presheaf.map U.unop.leTop.op s • x
  simp only [map_add,add_smul]
/-- Multiplication of original global sections gives composition in its
actual order on every original open; no cohomology scalar action is assumed. -/
theorem originalGlobalModuleScalar_mul (r s : Γ(X,⊤)) (M : X.Modules) :
    originalGlobalModuleScalar (r*s) M =
      originalGlobalModuleScalar s M ≫ originalGlobalModuleScalar r M := by
  apply SheafOfModules.hom_ext
  ext U x
  change X.presheaf.map U.unop.leTop.op (r*s) • x =
    X.presheaf.map U.unop.leTop.op r • (X.presheaf.map U.unop.leTop.op s • x)
  simp only [map_mul,mul_smul]
end LinearStudy
