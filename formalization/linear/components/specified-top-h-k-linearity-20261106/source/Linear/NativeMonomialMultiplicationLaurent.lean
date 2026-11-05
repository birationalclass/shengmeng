module
public import Linear.NativeCoordinatePolynomialMultiplication
public import Linear.NativeHomogeneousMultiplicationFrame
public import Linear.NativeHomogeneousLaurentMonomial
public import Linear.ProjectiveLaurentSectionShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual chart coefficient of an original homogeneous monomial
has precisely its expected Laurent coordinate. -/
theorem coordinateNativeMonomialChartCoefficient_laurent {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m : ℤ)) (hb : ∀ i, 0 ≤ b.1 i) :
    coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K) a
      (LinearStudy.nativeHomogeneousChartCoefficient (homogeneousSubmodule σ K) m
        ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩
        (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
        (coordinateOpenCechIntersection (R := K) a)
        (coordinateOpenCechIntersection_le (R := K) a 0)) =
    AddMonoidAlgebra.single
      (homogeneousLaurentShiftLocalExponent (fun j => (a j).down) b hb) 1 := by
  let c := LinearStudy.nativeHomogeneousChartCoefficient (homogeneousSubmodule σ K) m
    ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩
    (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
    (coordinateOpenCechIntersection (R := K) a)
    (coordinateOpenCechIntersection_le (R := K) a 0)
  have h := coordinateNativeHomogeneousMonomial_laurent (K := K) a m b hb (1 : K)
  have hframe : coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m : ℤ) c =
    (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (m : ℤ))).map
      (homOfLE (show coordinateOpenCechIntersection (R := K) a ≤ ⊤ from le_top)).op
      (LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m
        ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩) :=
    LinearStudy.nativePositiveHomogeneousGlobalSection_frame
    (homogeneousSubmodule σ K) m
    ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩
    (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
    (coordinateOpenCechIntersection (R := K) a)
    (coordinateOpenCechIntersection_le (R := K) a 0)
  rw [← hframe] at h
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a (m : ℤ)
    ((coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m : ℤ)).symm
      (coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m : ℤ) c)) = _ at h
  rw [LinearEquiv.symm_apply_apply, map_one] at h
  apply (AddMonoidAlgebra.mapDomainLinearEquiv
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    (coordinateLaurentExponentEquiv (fun j => (a j).down) (m : ℤ))).injective
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a (m : ℤ) c = _
  rw [AddMonoidAlgebra.mapDomainLinearEquiv_single]
  change _ = AddMonoidAlgebra.single
    ((coordinateLaurentExponentEquiv (fun j => (a j).down) (m : ℤ))
      ((coordinateLaurentExponentEquiv (fun j => (a j).down) (m : ℤ)).symm _)) 1
  rw [Equiv.apply_symm_apply]
  exact h

/-- On EVERY actual coordinate intersection, multiplication by the original
monomial on native twist sections corresponds to the proved Laurent shift. -/
theorem coordinateNativeMonomialMultiplication_laurent {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m : ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n a) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a (k+(m:ℤ))
      ((coordinateNativePolynomialMultiplication (K := K) (σ := σ) m
        ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k).val.app
        (op (coordinateOpenCechIntersection (R := K) a)) s) =
    homogeneousLaurentShiftLinear
      (R := Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))) _ b hb
      (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a k s) := by
  let r : (ProjectiveSpectrum.Proj.structureSheaf (homogeneousSubmodule σ K)).1.obj
      (op (coordinateOpenCechIntersection (R := K) a)) :=
    (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k).symm s
  let c := LinearStudy.nativeHomogeneousChartCoefficient (homogeneousSubmodule σ K) m
    ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩
    (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
    (coordinateOpenCechIntersection (R := K) a)
    (coordinateOpenCechIntersection_le (R := K) a 0)
  have hs : coordinateNativeIntegerTwistCechFactorFrame (K := K) a k r = s :=
    (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k).apply_symm_apply s
  have hmul : (coordinateNativePolynomialMultiplication (K := K) (σ := σ) m
      ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩ k).val.app
        (op (coordinateOpenCechIntersection (R := K) a))
        (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k r) =
      coordinateNativeIntegerTwistCechFactorFrame (K := K) a (k+(m:ℤ)) (c*r) :=
    LinearStudy.nativeHomogeneousMultiplication_frame (homogeneousSubmodule σ K) m
      ⟨monomial b.natExponent 1, b.natExponent_monomial_homogeneous m hb 1⟩
      (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
      (coordinateOpenCechIntersection (R := K) a)
      (coordinateOpenCechIntersection_le (R := K) a 0) k r
  rw [← hs, hmul]
  unfold coordinateNativeIntegerTwistCechFactorLaurentEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact coordinateHomogeneousLaurent_section_multiply a b hb _ r
    (coordinateNativeMonomialChartCoefficient_laurent a m b hb)
end MvPolynomial
