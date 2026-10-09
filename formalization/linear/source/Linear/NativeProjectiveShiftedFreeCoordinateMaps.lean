module
public import Linear.IntegerShiftedFreePieces
public import Linear.NativeProjectiveModuleSheafMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq ι] (w : ι → ℤ)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The original coordinate projection has its actual negative generator
degree, for the constructed integer grading of the shifted free module. -/
theorem integerShiftedFreeProjection_homogeneous (i : ι) (d : ℤ)
    (f : ι → S) (hf : f ∈ integerShiftedFreePiece 𝓑 w d) :
    (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) f ∈
      nativeProjectiveRingIntegerPiece 𝓑 (d + -w i) := by
  change ∀ j ∈ Set.univ, f j ∈ nativeProjectiveRingIntegerPiece 𝓑 (d - w j) at hf
  simpa only [LinearMap.proj_apply, sub_eq_add_neg] using hf i (Set.mem_univ i)

/-- The original single-coordinate inclusion has its actual generator
degree. No twist-sheaf comparison is assumed. -/
theorem integerShiftedFreeSingle_homogeneous (i : ι) (d : ℤ)
    (x : S) (hx : x ∈ nativeProjectiveRingIntegerPiece 𝓑 d) :
    (LinearMap.single (R := S) (φ := fun _ : ι => S) i) x ∈
      integerShiftedFreePiece 𝓑 w (d + w i) := by
  intro j hj
  by_cases h : j = i
  · subst j
    simp only [LinearMap.single_apply, Pi.single_eq_same, add_sub_cancel_right]
    change x ∈ nativeProjectiveRingIntegerPiece 𝓑 d
    exact hx
  · simp only [LinearMap.single_apply, Pi.single_eq_of_ne h]
    exact (nativeProjectiveRingIntegerPiece 𝓑 (d + w i - w j)).zero_mem

/-- Actual native sections of the shifted free module project to actual
integer-twist sections on the SAME original open. -/
def nativeShiftedFreeCoordinateSectionProjection (i : ι)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 U →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) U where
  toFun x := ⟨fun p => nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p), by
    change (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) (-w i)).pred
        (fun p => nativeProjectiveModuleAtPrimeMap 𝓑
          (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p))
    simpa only [zero_add] using nativeProjectiveModuleLocalPredicate_map 𝓑
      (integerShiftedFreePiece 𝓑 w) (nativeProjectiveRingIntegerPiece 𝓑) (-w i)
      (LinearMap.proj (R := S) (φ := fun _ : ι => S) i)
      (integerShiftedFreeProjection_homogeneous 𝓑 w i) 0 x.property⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1).map_add _ _
  map_smul' r x := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1).map_smul (r.1 p) (x.1 p)

/-- Actual native integer-twist sections inject into the shifted free
module sections on the SAME original open. -/
def nativeShiftedFreeCoordinateSectionInclusion (i : ι)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (-w i) U →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 w)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 0 U where
  toFun x := ⟨fun p => nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p), by
    change (nativeProjectiveModuleLocalPredicate 𝓑 (integerShiftedFreePiece 𝓑 w) 0).pred
      (fun p => nativeProjectiveModuleAtPrimeMap 𝓑
        (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1 (x.1 p))
    simpa only [neg_add_cancel] using nativeProjectiveModuleLocalPredicate_map 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) (integerShiftedFreePiece 𝓑 w) (w i)
      (LinearMap.single (R := S) (φ := fun _ : ι => S) i)
      (integerShiftedFreeSingle_homogeneous 𝓑 w i) (-w i) x.property⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1).map_add _ _
  map_smul' r x := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑
      (LinearMap.single (R := S) (φ := fun _ : ι => S) i) p.1).map_smul (r.1 p) (x.1 p)

end LinearStudy
