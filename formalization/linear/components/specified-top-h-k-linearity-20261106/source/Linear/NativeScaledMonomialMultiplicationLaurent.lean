module
public import Linear.NativeMonomialMultiplicationLaurent
public import Linear.ProjectiveLaurentScaledSectionShift
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

/-- The original chart coefficient of κX^b has coefficient κ transported
through the canonical Spec global-section ring isomorphism. -/
theorem coordinateNativeScaledMonomialChartCoefficient_laurent {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (κ : K) :
    coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K) a
      (LinearStudy.nativeHomogeneousChartCoefficient (homogeneousSubmodule σ K) m
        ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩
        (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
        (coordinateOpenCechIntersection (R := K) a)
        (coordinateOpenCechIntersection_le (R := K) a 0)) =
    AddMonoidAlgebra.single (homogeneousLaurentShiftLocalExponent (fun j => (a j).down) b hb)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) := by
  let c := LinearStudy.nativeHomogeneousChartCoefficient (homogeneousSubmodule σ K) m
    ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩
    (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
    (coordinateOpenCechIntersection (R := K) a) (coordinateOpenCechIntersection_le (R := K) a 0)
  have h := coordinateNativeHomogeneousMonomial_laurent (K := K) a m b hb κ
  have hframe : coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m:ℤ) c =
      (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (m:ℤ))).map
        (homOfLE (show coordinateOpenCechIntersection (R := K) a ≤ ⊤ from le_top)).op
        (LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m
          ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩) :=
    LinearStudy.nativePositiveHomogeneousGlobalSection_frame (homogeneousSubmodule σ K) m
      ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩
      (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
      (coordinateOpenCechIntersection (R := K) a) (coordinateOpenCechIntersection_le (R := K) a 0)
  rw [← hframe] at h
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a (m:ℤ)
    ((coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m:ℤ)).symm
      (coordinateNativeIntegerTwistCechFactorFrame (K := K) a (m:ℤ) c)) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  apply (AddMonoidAlgebra.mapDomainLinearEquiv
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))
    (coordinateLaurentExponentEquiv (fun j => (a j).down) (m:ℤ))).injective
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := K) a (m:ℤ) c = _
  rw [AddMonoidAlgebra.mapDomainLinearEquiv_single]
  change _ = AddMonoidAlgebra.single
    ((coordinateLaurentExponentEquiv (fun j => (a j).down) (m:ℤ))
      ((coordinateLaurentExponentEquiv (fun j => (a j).down) (m:ℤ)).symm _)) _
  rw [Equiv.apply_symm_apply]
  exact h

/-- On every actual coordinate intersection, original multiplication by
κX^b is the Laurent shift multiplied by the original transported coefficient. -/
theorem coordinateNativeScaledMonomialMultiplication_laurent {n : ℕ}
    (a : Fin (n+1) → ULift.{u} σ) (m : ℕ)
    (b : HomogeneousLaurentExponent σ (m:ℤ)) (hb : ∀ i, 0 ≤ b.1 i) (κ : K) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n a) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a (k+(m:ℤ))
      ((coordinateNativePolynomialMultiplication (K := K) (σ := σ) m
        ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k).val.app
        (op (coordinateOpenCechIntersection (R := K) a)) s) =
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm κ) •
      homogeneousLaurentShiftLinear
        (R := Γ(Spec (CommRingCat.of K), (⊤ : (Spec (CommRingCat.of K)).Opens))) _ b hb
        (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a k s) := by
  let r : (ProjectiveSpectrum.Proj.structureSheaf (homogeneousSubmodule σ K)).1.obj
      (op (coordinateOpenCechIntersection (R := K) a)) :=
    (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k).symm s
  let c := LinearStudy.nativeHomogeneousChartCoefficient (homogeneousSubmodule σ K) m
    ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩
    (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
    (coordinateOpenCechIntersection (R := K) a) (coordinateOpenCechIntersection_le (R := K) a 0)
  have hs : coordinateNativeIntegerTwistCechFactorFrame (K := K) a k r = s :=
    (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k).apply_symm_apply s
  have hmul : (coordinateNativePolynomialMultiplication (K := K) (σ := σ) m
      ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩ k).val.app
        (op (coordinateOpenCechIntersection (R := K) a))
        (coordinateNativeIntegerTwistCechFactorFrame (K := K) a k r) =
      coordinateNativeIntegerTwistCechFactorFrame (K := K) a (k+(m:ℤ)) (c*r) :=
    LinearStudy.nativeHomogeneousMultiplication_frame (homogeneousSubmodule σ K) m
      ⟨monomial b.natExponent κ, b.natExponent_monomial_homogeneous m hb κ⟩
      (X (a 0).down) (X_mem_homogeneousSubmodule_one K (a 0).down)
      (coordinateOpenCechIntersection (R := K) a) (coordinateOpenCechIntersection_le (R := K) a 0) k r
  rw [← hs, hmul]
  unfold coordinateNativeIntegerTwistCechFactorLaurentEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact coordinateHomogeneousLaurent_section_scaled_multiply a b hb _ _ r
    (coordinateNativeScaledMonomialChartCoefficient_laurent a m b hb κ)

end MvPolynomial
