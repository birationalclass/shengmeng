module
public import Linear.NativeIntegerFreeTwistRegrading
public import Linear.NativeIntegerTwistDegreeTransport
public import Linear.NativeShiftedFreeSheafMatrixEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S I : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq I] (w : I → ℤ)

/-- ORIGINAL free coordinate projection for ANY integer twist k,
constructed by actual identity regrading and the original coordinate map. -/
def nativeIntegerShiftedFreeCoordinateProjection (k : ℤ) (i : I) :
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k ⟶
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i) :=
  (nativeIntegerFreeTwistRegradingIso 𝓑 w k).inv ≫
    nativeShiftedFreeCoordinateSheafProjection 𝓑 (fun i => w i-k) i ≫
      nativeRingIntegerTwistDegreeCast 𝓑 (by omega)

/-- ORIGINAL free coordinate inclusion for ANY integer twist k. -/
def nativeIntegerShiftedFreeCoordinateInclusion (k : ℤ) (i : I) :
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i) ⟶
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k :=
  nativeRingIntegerTwistDegreeCast 𝓑 (by omega) ≫
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 (fun i => w i-k) i ≫
      (nativeIntegerFreeTwistRegradingIso 𝓑 w k).hom

/-- The actual projection keeps the SAME original localized coordinate,
without an assumed frame or coordinate comparison. -/
theorem nativeIntegerShiftedFreeCoordinateProjection_value (k : ℤ) (i : I)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U) (p : U.unop) :
    (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U) x).1 p =
      nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.proj (R := S) (φ := fun _ : I => S) i) p.1 (x.1 p) := by
  unfold nativeIntegerShiftedFreeCoordinateProjection
  change (((nativeRingIntegerTwistDegreeCast 𝓑 (by omega : -(w i-k) = k-w i)).val.app U)
    (((nativeShiftedFreeCoordinateSheafProjection 𝓑 (fun i => w i-k) i).val.app U)
      (((nativeIntegerFreeTwistRegradingIso 𝓑 w k).inv.val.app U) x))).1 p = _
  rw [nativeRingIntegerTwistDegreeCast_value]
  rfl

/-- The actual inclusion keeps the SAME original localized single
coordinate,for every integer k and every original open. -/
theorem nativeIntegerShiftedFreeCoordinateInclusion_value (k : ℤ) (i : I)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-w i) U) (p : U.unop) :
    (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U) x).1 p =
      nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.single (R := S) (φ := fun _ : I => S) i) p.1 (x.1 p) := by
  unfold nativeIntegerShiftedFreeCoordinateInclusion
  change nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.single (R := S) (φ := fun _ : I => S) i) p.1
        ((((nativeRingIntegerTwistDegreeCast 𝓑 (by omega : k-w i = -(w i-k))).val.app U) x).1 p) = _
  rw [nativeRingIntegerTwistDegreeCast_value]

/-- Every ACTUAL coordinate component of the ORIGINAL homogeneous free
map,at ANY integer twist,has its SAME original scalar-entry value. -/
theorem nativeIntegerShiftedFreeSheaf_matrixEntry_value
    {J : Type} [DecidableEq J] (z : I → ℤ) (c : (I → S) →ₗ[S] (J → S)) (w' : J → ℤ)
    (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
      c x ∈ integerShiftedFreePiece 𝓑 w' d)
    (k : ℤ) (i : I) (j : J) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-z i) U) (p : U.unop) :
    (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 z k i ≫
        nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
          (integerShiftedFreePiece 𝓑 w') (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
          (integerShiftedFreePiece_smul_homogeneous 𝓑 w') c hc k ≫
        nativeIntegerShiftedFreeCoordinateProjection 𝓑 w' k j).val.app U) x).1 p =
      integerShiftedFreeMapEntry c i j • x.1 p := by
  change (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w' k j).val.app U)
    (((nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
      (integerShiftedFreePiece 𝓑 w') (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w') c hc k).val.app U)
        (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 z k i).val.app U) x))).1 p = _
  rw [nativeIntegerShiftedFreeCoordinateProjection_value]
  change nativeProjectiveModuleAtPrimeMap 𝓑
    (LinearMap.proj (R := S) (φ := fun _ : J => S) j) p.1
      (nativeProjectiveModuleAtPrimeMap 𝓑 c p.1
        ((((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 z k i).val.app U) x).1 p)) = _
  rw [nativeIntegerShiftedFreeCoordinateInclusion_value, nativeShiftedFreePrime_matrixEntry]
  exact nativeProjectiveHomogeneousSMul_prime_value 𝓑 (integerShiftedFreeMapEntry c i j) p.1 (x.1 p)

end LinearStudy
