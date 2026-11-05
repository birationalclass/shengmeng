module
public import Linear.NativeShiftedFreeSheafMatrixEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K S I J : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [DecidableEq I] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hh : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z d →
  c x ∈ integerShiftedFreePiece 𝓑 w d)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- Negative original entry degree forces the ACTUAL original sheaf
coordinate component to be the zero morphism. This is derived from the
original relation map's homogeneous grading,not supplied as a matrix input. -/
theorem nativeShiftedFreeSheaf_matrixEntry_zero (i : I) (j : J) (h : z i < w j) :
    nativeShiftedFreeCoordinateSheafInclusion 𝓑 z i ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 z)
        (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 z)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) c hh 0 ≫
      nativeShiftedFreeCoordinateSheafProjection 𝓑 w j = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext p
  change _ = 0
  erw [nativeShiftedFreeSheaf_matrixEntry_value 𝓑 c z w hh i j U s p]
  rw [integerShiftedFreeMapEntry_eq_zero 𝓑 z w c hh i j h,zero_smul]

end LinearStudy
