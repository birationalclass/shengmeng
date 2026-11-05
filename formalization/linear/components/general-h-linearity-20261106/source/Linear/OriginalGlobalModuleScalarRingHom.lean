module
public import Linear.OriginalGlobalModuleScalarRingLaws
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
/-- The ORIGINAL global sections act through their actual coefficient
endomorphisms. This is independent of any cohomology comparison choice. -/
def originalGlobalModuleScalarRingHom (M : X.Modules) : Γ(X,⊤) →+* End M where
  toFun r := originalGlobalModuleScalar r M
  map_one' := originalGlobalModuleScalar_one M
  map_mul' r s := originalGlobalModuleScalar_mul r s M
  map_zero' := originalGlobalModuleScalar_zero M
  map_add' r s := originalGlobalModuleScalar_add r s M
end LinearStudy
