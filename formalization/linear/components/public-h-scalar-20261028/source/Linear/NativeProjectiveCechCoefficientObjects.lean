module
public import Linear.NativeTwistRegradingCoefficientSquares
public import Linear.OrderedCechModuleScalarNaturality
public import Linear.SchemeModuleFiniteSupportCohomology
public import Linear.NativeProjectiveTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
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
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Limits
variable {ι : Type u} [LinearOrder ι] (U : ι → (Proj A).Opens)
attribute [local irreducible] orderedFormalCechComplex FormalCoproduct.evalOp
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf schemeModuleToActualAbelianSheaf
  nativeProjectiveTwistRegradingIso
/-- The EXACT original ordered Cech coefficient map,with both native sheaves cached. -/
def nativeProjectiveOrderedCechCoefficientMap (k : ℤ) :
    orderedTopAbelianCechComplex (Proj A) U
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hD k)) ⟶
    orderedTopAbelianCechComplex (Proj A) U
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A E hE k)) :=
  orderedTopAbelianCechCoefficientMap (Proj A) U
    ((schemeModuleToActualAbelianSheaf (Proj A)).map (nativeProjectiveDegreeZeroSheafMap A D E hD hE f hf k))
/-- The EXACT original Cech regrading iso,without changing the coefficient action. -/
def nativeProjectiveOrderedCechRegradingIso (k : ℤ) :
    orderedTopAbelianCechComplex (Proj A) U
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A (integerGradingShift D k)
        (integerGradingShift_smul_homogeneous A D hD k) 0)) ≅
    orderedTopAbelianCechComplex (Proj A) U
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A D hD k)) :=
  orderedTopAbelianCechCoefficientIso U
    ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso (nativeProjectiveTwistRegradingIso A D hD k))
end LinearStudy
