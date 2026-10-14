module
public import Linear.NativeCoordinatePolynomialMultiplication
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] LinearStudy.nativeProjectiveAtPrimeModuleScalar

/-- The originally constructed sheaf multiplication is additive in
the original homogeneous polynomial, on every actual open and point. -/
theorem coordinateNativePolynomialMultiplication_add (m : ℕ)
    (p q : homogeneousSubmodule σ K m) (k : ℤ) :
    coordinateNativePolynomialMultiplication (K := K) m (p+q) k =
      coordinateNativePolynomialMultiplication (K := K) m p k +
        coordinateNativePolynomialMultiplication (K := K) m q k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  change (((coordinateNativePolynomialMultiplication m (p+q) k).val.app U) s).1 x =
    (((coordinateNativePolynomialMultiplication m p k).val.app U) s).1 x +
      (((coordinateNativePolynomialMultiplication m q k).val.app U) s).1 x
  rw [coordinateNativePolynomialMultiplication_value,
    coordinateNativePolynomialMultiplication_value, coordinateNativePolynomialMultiplication_value]
  exact add_smul p.1 q.1 (s.1 x)

theorem coordinateNativePolynomialMultiplication_zero (m : ℕ) (k : ℤ) :
    coordinateNativePolynomialMultiplication (K := K) (σ := σ) m 0 k = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  change (((coordinateNativePolynomialMultiplication (K := K) (σ := σ) m 0 k).val.app U) s).1 x = 0
  rw [coordinateNativePolynomialMultiplication_value]
  exact zero_smul _ _

/-- Actual additive dependence on p, before any Cech or duality comparison. -/
def coordinateNativePolynomialMultiplicationAddHom (m : ℕ) (k : ℤ) :
    homogeneousSubmodule σ K m →+
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k ⟶
        coordinateNativeIntegerTwist (K := K) (σ := σ) (k+(m:ℤ))) where
  toFun p := coordinateNativePolynomialMultiplication m p k
  map_zero' := coordinateNativePolynomialMultiplication_zero m k
  map_add' p q := coordinateNativePolynomialMultiplication_add m p q k

end MvPolynomial
