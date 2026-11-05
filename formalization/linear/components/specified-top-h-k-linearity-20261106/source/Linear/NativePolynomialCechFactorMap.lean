module
public import Linear.NativeCoordinatePolynomialMultiplication
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K : Type u} [Field K] {σ : Type}

/-- Apply the actual base-section functor to original polynomial sheaf
multiplication. Its construction uses no Laurent or duality transport. -/
def coordinateNativePolynomialCechFactorMap {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (p : homogeneousSubmodule σ K m) (k : ℤ) :
    Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n a ⟶
    Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (k+(m:ℤ)))
      (coordinateOpenCover (R := K) (σ := σ)) n a :=
  ((Scheme.Modules.baseModulePresheafFunctor (homogeneousProjπ (R := K) (σ := σ))).map
    (coordinateNativePolynomialMultiplication m p k)).app
    (op (coordinateOpenCechIntersection (R := K) a))

theorem coordinateNativePolynomialCechFactorMap_apply {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (p : homogeneousSubmodule σ K m) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n a) :
    coordinateNativePolynomialCechFactorMap a m p k s =
      (coordinateNativePolynomialMultiplication m p k).val.app
        (op (coordinateOpenCechIntersection (R := K) a)) s := rfl
end MvPolynomial
