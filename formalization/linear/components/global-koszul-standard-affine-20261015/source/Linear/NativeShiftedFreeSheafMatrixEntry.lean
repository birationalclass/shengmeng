module
public import Linear.IntegerShiftedFreeMatrix
public import Linear.NativeProjectiveShiftedFreeSheafMaps
public import Linear.NativeProjectiveDegreeZeroComposition
public import Linear.NativeProjectiveHomogeneousSMul
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K S I J : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [DecidableEq I]
variable (c : (I → S) →ₗ[S] (J → S))
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- At each ACTUAL original projective prime,the coordinate component
of the localized original free map is multiplication by its original
matrix entry. This is independent of any chosen duality coordinates. -/
theorem nativeShiftedFreePrime_matrixEntry (i : I) (j : J) (p : ProjectiveSpectrum 𝓑)
    (x : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.proj (R := S) (φ := fun _ : J => S) j) p
      (nativeProjectiveModuleAtPrimeMap 𝓑 c p
        (nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.single (R := S) (φ := fun _ : I => S) i) p x)) =
    nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.lsmul S S (integerShiftedFreeMapEntry c i j)) p x := by
  induction x using LocalizedModule.induction_on with
  | h x den =>
    rw [nativeProjectiveModuleAtPrimeMap_mk,nativeProjectiveModuleAtPrimeMap_mk,
      nativeProjectiveModuleAtPrimeMap_mk,nativeProjectiveModuleAtPrimeMap_mk]
    simp only [LinearMap.single_apply,LinearMap.proj_apply,LinearMap.lsmul_apply]
    have hs : Pi.single i x = x • Pi.single i (1:S) := by
      simpa only [smul_eq_mul,mul_one] using Pi.single_smul' i x (1:S)
    rw [hs,map_smul]
    simp only [Pi.smul_apply,smul_eq_mul,integerShiftedFreeMapEntry,mul_comm]

variable [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
  c x ∈ integerShiftedFreePiece 𝓑 w d)

/-- On EVERY original open,the ACTUAL sheaf coordinate component
multiplies original-prime section values by its original homogeneous
matrix entry. Its degree and negative-degree zero are proved separately. -/
theorem nativeShiftedFreeSheaf_matrixEntry_value (i : I) (j : J)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (s : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-z i) U) (p : U.unop) :
    (((nativeShiftedFreeCoordinateSheafInclusion 𝓑 z i ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w j).val.app U s).1 p) =
      integerShiftedFreeMapEntry c i j • s.1 p := by
  change nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.proj (R := S) (φ := fun _ : J => S) j) p.1
      (nativeProjectiveModuleAtPrimeMap 𝓑 c p.1
        (nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.single (R := S) (φ := fun _ : I => S) i) p.1 (s.1 p))) = _
  erw [nativeShiftedFreePrime_matrixEntry 𝓑 c i j p.1 (s.1 p)]
  exact nativeProjectiveHomogeneousSMul_prime_value 𝓑 (integerShiftedFreeMapEntry c i j) p.1 (s.1 p)

end LinearStudy
