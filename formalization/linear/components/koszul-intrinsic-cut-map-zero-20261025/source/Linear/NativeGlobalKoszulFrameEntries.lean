module
public import Linear.NativeProjectiveKoszulComplex
public import Linear.NativeIntegerShiftedFreeCoordinateMaps
public import Linear.NativeHomogeneousIntegerFrameMultiply
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Every coordinate entry of the SAME ACTUAL GLOBAL Koszul differential,
in ORIGINAL a-frames at ANY integer twist,equals multiplication by its
SAME original dehomogenized exterior-differential entry D_ji/a^q.
The degree-q numerator is DERIVED from original H;it is not supplied. -/
theorem nativeGlobalKoszulDifferential_frameEntry {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (k : ℤ)
    (i : Set.powersetCard (Fin r) (p+1)) (j : Set.powersetCard (Fin r) p)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (s : (Proj 𝓑).presheaf.obj (op U)) :
    let ell : 𝓑 q := ⟨integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j,
      homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p i j⟩
    (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑
          (fun _ : Set.powersetCard (Fin r) (p+1) => ((p+1:ℕ):ℤ)*(q:ℤ)) k i ≫
        nativeProjectiveKoszulDifferential 𝓑 H hH p k ≫
        nativeIntegerShiftedFreeCoordinateProjection 𝓑
          (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k j).val.app (op U))
      (nativeIntegerTwistSectionFrame 𝓑 a ha (k-((p+1:ℕ):ℤ)*(q:ℤ))
        (op U) (fun t => hU t.2) s)) =
      nativeIntegerTwistSectionFrame 𝓑 a ha (k-(p:ℤ)*(q:ℤ)) (op U) (fun t => hU t.2)
        (nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU * s) := by
  dsimp only
  apply Subtype.ext
  funext t
  change (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑
      (fun _ : Set.powersetCard (Fin r) (p+1) => ((p+1:ℕ):ℤ)*(q:ℤ)) k i ≫
    nativeProjectiveDegreeZeroSheafMap 𝓑 _ _ _ _
      (homogeneousKoszulCoordinateDifferential H p)
      (homogeneousKoszulCoordinateDifferential_homogeneous 𝓑 H hH p) k ≫
    nativeIntegerShiftedFreeCoordinateProjection 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k j).val.app (op U))
    (nativeIntegerTwistSectionFrame 𝓑 a ha (k-((p+1:ℕ):ℤ)*(q:ℤ))
      (op U) (fun t => hU t.2) s)).1 t = _
  erw [nativeIntegerShiftedFreeSheaf_matrixEntry_value]
  let ell : 𝓑 q := ⟨integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j,
    homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p i j⟩
  have hframe := congrArg (fun x => x.1 t)
    (nativeIntegerTwistSectionFrame_homogeneous_multiply 𝓑 q ell a ha U hU
      (k-((p+1:ℕ):ℤ)*(q:ℤ)) s)
  rw [nativeProjectiveHomogeneousSMul_section_value] at hframe
  change (ell:S) • _ = nativePrimeIntegerTwistEquiv 𝓑 t.1 a (hU t.2)
    (k-((p+1:ℕ):ℤ)*(q:ℤ)+(q:ℤ))
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 t.1
        ((nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU * s).1 t)) at hframe
  change (ell:S) • _ = nativePrimeIntegerTwistEquiv 𝓑 t.1 a (hU t.2)
    (k-(p:ℤ)*(q:ℤ))
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 t.1
        ((nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU * s).1 t))
  have hd : k-((p+1:ℕ):ℤ)*(q:ℤ)+(q:ℤ) = k-(p:ℤ)*(q:ℤ) := by push_cast; ring
  rw [hd] at hframe
  exact hframe

end LinearStudy
