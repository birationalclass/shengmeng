module
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeProjectiveShiftedFreeBiproduct
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq ι] [Fintype ι] (w : ι → ℤ)

local instance nativeShiftedTwistHasFiniteBiproducts :
    HasFiniteBiproducts (AlgebraicGeometry.Proj 𝓑).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem nativeShiftedFreeSheaf_grading_congr
    {D₁ D₂ : ℤ → Submodule K (ι → S)}
    (h₁ : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
      ∀ x : ι → S, x ∈ D₁ d → c • x ∈ D₁ ((n : ℤ)+d))
    (h₂ : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
      ∀ x : ι → S, x ∈ D₂ d → c • x ∈ D₂ ((n : ℤ)+d))
    (h : D₁ = D₂) :
    nativeProjectiveModuleSheaf 𝓑 D₁ h₁ 0 =
      nativeProjectiveModuleSheaf 𝓑 D₂ h₂ 0 := by
  cases h
  rfl

/-- Regrading the actual shifted free module subtracts the twist from every
generator degree, on the same underlying module. -/
theorem integerGradingShift_shiftedFreePiece (k : ℤ) :
    integerGradingShift (integerShiftedFreePiece 𝓑 w) k =
      integerShiftedFreePiece 𝓑 (fun i => w i - k) := by
  funext d
  unfold integerGradingShift integerShiftedFreePiece
  congr 1
  funext i
  congr 1
  dsimp only
  omega

/-- Actual degree-k sheaf of a shifted finite free module is the finite
biproduct of the actual coordinate twists of degree k minus generator degree.
The comparison uses the original fraction sheaf and its proved regrading. -/
def nativeShiftedFreeIntegerTwistBiproductIso (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k ≅
    biproduct (fun i : ι => nativeProjectiveModuleSheaf 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k - w i)) := by
  have he := integerGradingShift_shiftedFreePiece 𝓑 w k
  let e := (nativeProjectiveTwistRegradingIso 𝓑 (integerShiftedFreePiece 𝓑 w)
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k).symm
  have hSheaf : nativeProjectiveModuleSheaf 𝓑
      (integerGradingShift (integerShiftedFreePiece 𝓑 w) k)
      (integerGradingShift_smul_homogeneous 𝓑 (integerShiftedFreePiece 𝓑 w)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k) 0 =
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
      (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 := by
    exact nativeShiftedFreeSheaf_grading_congr 𝓑 _ _ he
  have hFamilies : (fun i : ι => nativeProjectiveModuleSheaf 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-(w i-k))) =
    (fun i : ι => nativeProjectiveModuleSheaf 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i)) := by
    funext i
    congr 1
    omega
  exact e ≪≫ eqToIso hSheaf ≪≫
    nativeShiftedFreeSheafBiproductIso 𝓑 (fun i => w i-k) ≪≫
    eqToIso (congrArg (fun A => biproduct A) hFamilies)

end LinearStudy
