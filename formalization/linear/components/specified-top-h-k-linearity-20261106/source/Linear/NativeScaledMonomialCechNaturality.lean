module
public import Linear.NativeScaledMonomialMultiplicationLaurent
public import Linear.NativePolynomialCechFactorMap
public import Linear.ProjectiveLaurentCechScalarShift
public import Linear.ProjectiveLaurentShiftComplex
public import Linear.ModuleOrderedBaseCechFunctor
public import Mathlib.Algebra.Homology.Linear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem coordinateNativeScaledMonomialCechFactor_naturality {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (κ : K) (k : ℤ) :
    (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a k).toModuleIso.hom ≫
      (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) •
        ModuleCat.ofHom (homogeneousLaurentShiftLinear _ b hb)) =
    coordinateNativePolynomialCechFactorMap (K := K) a m
      ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k ≫
      (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a (k+(m:ℤ))).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (coordinateNativeScaledMonomialMultiplication_laurent a m b hb κ k s).symm

/-- The original sheaf multiplication by κX^b gives the actual
coefficient-scaled Laurent shift on the full native Cech complex. -/
theorem coordinateNativeScaledMonomialCechComplex_naturality (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (κ : K) (k : ℤ) :
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) k).hom ≫
      (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) •
        coordinateLaurentShiftComplex b hb) =
    (Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ))).map
        (coordinateNativePolynomialMultiplication (K := K) m
          ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k) ≫
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) (k+(m:ℤ))).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k n).hom ≫
    (((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) •
      coordinateLaurentCechShift b hb n) =
    (Scheme.Modules.orderedBaseCechObjectFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ)) n).map
        (coordinateNativePolynomialMultiplication (K := K) m
          ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k) ≫
      (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) (k+(m:ℤ)) n).hom
  rw [coordinateLaurentCechShift_scalar_lift]
  unfold coordinateNativeLaurentOrderedCechObjectIso coordinateLaurentTupleProjection
  have hmap : (Scheme.Modules.orderedBaseCechObjectFunctor
      (homogeneousProjπ (R := K) (σ := σ)) (coordinateOpenCover (R := K) (σ := σ)) n).map
      (coordinateNativePolynomialMultiplication (K := K) m
        ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k) =
      Limits.Pi.map (fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        coordinateNativePolynomialCechFactorMap (K := K) a.1 m
          ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k) := rfl
  rw [hmap]
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc]
  conv_rhs => erw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc, Limits.Pi.map_π]
  rw [Category.assoc]
  apply congrArg (fun f => Pi.π _ a ≫ f)
  exact coordinateNativeScaledMonomialCechFactor_naturality a.1 m b hb κ k

end MvPolynomial
