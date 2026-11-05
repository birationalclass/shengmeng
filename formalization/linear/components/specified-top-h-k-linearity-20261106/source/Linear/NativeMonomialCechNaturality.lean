module
public import Linear.NativePolynomialCechFactorMap
public import Linear.NativeMonomialMultiplicationLaurent
public import Linear.ProjectiveLaurentShiftComplex
public import Linear.ModuleOrderedBaseCechFunctor
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

theorem coordinateNativeMonomialCechFactor_naturality {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (k : ℤ) :
    (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a k).toModuleIso.hom ≫
      ModuleCat.ofHom (homogeneousLaurentShiftLinear _ b hb) =
    coordinateNativePolynomialCechFactorMap (K := K) a m
      ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k ≫
      (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a (k+(m:ℤ))).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (coordinateNativeMonomialMultiplication_laurent a m b hb k s).symm

/-- The actual Cech functor applied to original monomial sheaf multiplication
intertwines with the independently constructed Laurent cochain shift. -/
theorem coordinateNativeMonomialCechComplex_naturality (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (k : ℤ) :
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) k).hom ≫
      coordinateLaurentShiftComplex b hb =
    (Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ))).map
        (coordinateNativePolynomialMultiplication (K := K) m
          ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k) ≫
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) (k+(m:ℤ))).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) k n).hom ≫
    coordinateLaurentCechShift b hb n =
    (Scheme.Modules.orderedBaseCechObjectFunctor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateOpenCover (R := K) (σ := σ)) n).map
        (coordinateNativePolynomialMultiplication (K := K) m
          ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k) ≫
      (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) (k+(m:ℤ)) n).hom
  unfold coordinateNativeLaurentOrderedCechObjectIso coordinateLaurentCechShift
  have hmap : (Scheme.Modules.orderedBaseCechObjectFunctor
      (homogeneousProjπ (R := K) (σ := σ)) (coordinateOpenCover (R := K) (σ := σ)) n).map
      (coordinateNativePolynomialMultiplication (K := K) m
        ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k) =
      Limits.Pi.map (fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        coordinateNativePolynomialCechFactorMap (K := K) a.1 m
          ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k) := rfl
  rw [hmap]
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc]
  conv_rhs => erw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc, Limits.Pi.map_π]
  rw [Category.assoc]
  apply congrArg (fun f => Pi.π _ a ≫ f)
  exact coordinateNativeMonomialCechFactor_naturality a.1 m b hb k

/-- The same square holds on every actual Cech homology object, by
the existing mathlib homology functor applied to the proved cochain square. -/
theorem coordinateNativeMonomialCechHomology_naturality (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (k : ℤ) (n : ℕ) :
    HomologicalComplex.homologyMap
      (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) k).hom n ≫
        coordinateLaurentShiftHomology b hb n =
    HomologicalComplex.homologyMap
      ((Scheme.Modules.orderedBaseCechComplexFunctor (homogeneousProjπ (R := K) (σ := σ))
        (coordinateOpenCover (R := K) (σ := σ))).map
          (coordinateNativePolynomialMultiplication (K := K) m
            ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k)) n ≫
      HomologicalComplex.homologyMap
        (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) (k+(m:ℤ))).hom n := by
  unfold coordinateLaurentShiftHomology
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    coordinateNativeMonomialCechComplex_naturality]
end MvPolynomial
