module
public import Linear.NativeIntegerTwistBaseSections
public import Linear.ProjectiveCechLaurentRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual integer twist of the polynomial graded ring on its
original Proj scheme, constructed from actual homogeneous fractions. -/
abbrev coordinateNativeIntegerTwist (k : ℤ) :
    (Proj (homogeneousSubmodule σ K)).Modules :=
  LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
    (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
    (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K)) k

/-- The actual intersection lies in every coordinate's nonvanishing
open, hence that coordinate is not in any of its original primes. -/
theorem coordinateOpenCechIntersection_coordinate_notMem {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : Fin (n + 1))
    (p : coordinateOpenCechIntersection (R := K) a) :
    X (a j).down ∉ p.1.asHomogeneousIdeal :=
  coordinateOpenCechIntersection_le (R := K) a j p.2

/-- The anchor coordinate gives an actual base-linear frame on every
standard Cech intersection for every integer twist. -/
def coordinateNativeIntegerTwistCechFactorFrame {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (k : ℤ) :
    Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (SheafOfModules.unit (Proj (homogeneousSubmodule σ K)).ringCatSheaf)
      (coordinateOpenCover (R := K) (σ := σ)) n a ≃ₗ[
        Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))]
      Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
        (coordinateOpenCover (R := K) (σ := σ)) n a :=
  LinearStudy.nativeIntegerTwistBaseSectionEquiv (homogeneousSubmodule σ K)
    (homogeneousProjπ (R := K) (σ := σ)) (X (a 0).down)
    (X_mem_homogeneousSubmodule_one K (a 0).down) k
    (op (coordinateOpenCechIntersection (R := K) a))
    (coordinateOpenCechIntersection_coordinate_notMem (K := K) a 0)

/-- An ACTUAL native integer-twist Cech factor is the free base module
on its allowed global homogeneous Laurent weights of total degree k. -/
def coordinateNativeIntegerTwistCechFactorLaurentEquiv {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (k : ℤ) :
    Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n a ≃ₗ[
        Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))]
      AddMonoidAlgebra
        Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
        {e : HomogeneousLaurentExponent σ k // e.IsAllowedOn (fun j => (a j).down)} :=
  (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k).symm.trans
    (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a k)

end MvPolynomial
