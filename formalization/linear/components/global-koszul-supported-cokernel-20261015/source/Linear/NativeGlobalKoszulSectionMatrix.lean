module
public import Linear.NativeIntegerShiftedFreeSectionFrames
public import Linear.NativeGlobalKoszulFrameEntries
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The ENTIRE original finite free frame commutes with EVERY original
open restriction,for arbitrary weights and EVERY integer twist. -/
theorem nativeIntegerShiftedFreeSectionFrame_restrict
    {I : Type} [DecidableEq I] [Fintype I] (w : I → ℤ) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (f : U ⟶ V)
    (hp : ∀ t : U.unop, a ∉ t.1.asHomogeneousIdeal)
    (v : I → (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) :
    (nativeProjectiveModulePresheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k).map f
        (nativeIntegerShiftedFreeSectionFrame 𝓑 w k a ha U hp v) =
      nativeIntegerShiftedFreeSectionFrame 𝓑 w k a ha V (fun t => hp (f.unop t))
        (fun i => (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.map f (v i)) := by
  change (nativeProjectiveModulePresheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k).map f
        (∑ i : I, ((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U)
          (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp (v i))) = _
  rw [map_sum]
  change (∑ i : I, _) = ∑ i : I, _
  apply Finset.sum_congr rfl
  intro i hi
  have hn := PresheafOfModules.naturality_apply
    (nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val f
      (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp (v i))
  exact hn.symm.trans (congrArg
    (fun x => ((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app V) x)
      (nativeIntegerTwistSectionFrame_restrict 𝓑 a ha (k-w i) f hp (v i)))

/-- Whole-map formula for the SAME ACTUAL GLOBAL Koszul differential in
original a-coordinate frames. Every original matrix numerator is DERIVED
from H. This assembles ALL entries;no desired matrix equation is an input. -/
theorem nativeGlobalKoszulDifferential_sectionFrame {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a)
    (v : Set.powersetCard (Fin r) (p+1) → (Proj 𝓑).presheaf.obj (op U)) :
    ((nativeProjectiveKoszulDifferential 𝓑 H hH p k).val.app (op U))
      (nativeIntegerShiftedFreeSectionFrame 𝓑
        (fun _ : Set.powersetCard (Fin r) (p+1) => ((p+1:ℕ):ℤ)*(q:ℤ))
          k a ha (op U) (fun t => hU t.2) v) =
    nativeIntegerShiftedFreeSectionFrame 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ))
        k a ha (op U) (fun t => hU t.2)
          (fun j => ∑ i : Set.powersetCard (Fin r) (p+1),
            nativeHomogeneousChartCoefficientSection 𝓑 q
              ⟨integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j,
                homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p i j⟩
              a ha U hU * v i) := by
  apply (nativeIntegerShiftedFreeSectionFrame 𝓑
    (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ))
      k a ha (op U) (fun t => hU t.2)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext j
  apply (nativeIntegerTwistSectionFrame 𝓑 a ha (k-(p:ℤ)*(q:ℤ))
    (op U) (fun t => hU t.2)).injective
  change nativeIntegerTwistSectionFrame 𝓑 a ha (k-(p:ℤ)*(q:ℤ))
    (op U) (fun t => hU t.2)
      ((nativeIntegerTwistSectionFrame 𝓑 a ha (k-(p:ℤ)*(q:ℤ))
        (op U) (fun t => hU t.2)).symm
          (((nativeIntegerShiftedFreeCoordinateProjection 𝓑
            (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k j).val.app (op U))
              (((nativeProjectiveKoszulDifferential 𝓑 H hH p k).val.app (op U))
                (nativeIntegerShiftedFreeSectionFrame 𝓑
                  (fun _ : Set.powersetCard (Fin r) (p+1) => ((p+1:ℕ):ℤ)*(q:ℤ))
                    k a ha (op U) (fun t => hU t.2) v)))) = _
  rw [LinearEquiv.apply_symm_apply]
  change ((nativeIntegerShiftedFreeCoordinateProjection 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k j).val.app (op U))
    (((nativeProjectiveKoszulDifferential 𝓑 H hH p k).val.app (op U))
      (∑ i : Set.powersetCard (Fin r) (p+1),
        ((nativeIntegerShiftedFreeCoordinateInclusion 𝓑
          (fun _ : Set.powersetCard (Fin r) (p+1) => ((p+1:ℕ):ℤ)*(q:ℤ)) k i).val.app (op U))
            (nativeIntegerTwistSectionFrame 𝓑 a ha (k-((p+1:ℕ):ℤ)*(q:ℤ))
              (op U) (fun t => hU t.2) (v i)))) = _
  rw [map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact nativeGlobalKoszulDifferential_frameEntry 𝓑 H hH p k i j a ha U hU (v i)

end LinearStudy
