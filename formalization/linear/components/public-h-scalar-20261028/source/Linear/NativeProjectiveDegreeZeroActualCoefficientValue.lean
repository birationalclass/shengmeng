module
public import Linear.NativeProjectiveDegreeZeroMap
public import Linear.SchemeModuleFiniteSupportCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[R] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
/-- Forgetting the ORIGINAL degree-zero native module-sheaf map to the
ACTUAL abelian sheaf preserves its ORIGINAL section formula,for EVERY
integer twist and EVERY original open. No replacement map is introduced. -/
theorem nativeProjectiveDegreeZeroActualAbelian_app (k : ℤ) (U : (Proj A).Opens)
    (x : nativeProjectiveModuleSections A D hD k (op U)) :
    (((schemeModuleToActualAbelianSheaf (Proj A)).map
      (nativeProjectiveDegreeZeroSheafMap A D E hD hE f hf k)).hom.app (op U)) x =
        nativeProjectiveDegreeZeroSectionMap A D E hD hE f hf k (op U) x := rfl
end LinearStudy
