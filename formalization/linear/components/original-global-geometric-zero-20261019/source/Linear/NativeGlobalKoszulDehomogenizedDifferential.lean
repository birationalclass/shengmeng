module
public import Linear.KoszulCoordinateEntryNaturality
public import Linear.NativeGlobalKoszulSectionMatrix
public import Linear.NativeCoordinateRatio
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The SAME original degree-q Koszul matrix entry divided by a^q is
EXACTLY the standard Koszul entry of the SAME ORIGINAL forms H_i/a^q.
Proved in actual structure-ring sections,not assumed as an affine comparison. -/
theorem nativeHomogeneousKoszulEntry_dehomogenize {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ)
    (i : Set.powersetCard (Fin r) (p+1)) (j : Set.powersetCard (Fin r) p)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) :
    nativeHomogeneousChartCoefficientSection 𝓑 q
      ⟨integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j,
        homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p i j⟩ a ha U hU =
    integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential
      (fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU) p) i j := by
  apply Subtype.ext
  funext t
  apply HomogeneousLocalization.val_injective
  let E := nativeStructureSectionPointRingHom 𝓑 (op U) t
  let A := algebraMap S (Localization t.1.asHomogeneousIdeal.toIdeal.primeCompl)
  let u := nativePrimeCoordinateUnit 𝓑 t.1 a (hU t.2) ^ (q:ℤ)
  let h := fun l : Fin r => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU
  change E (nativeHomogeneousChartCoefficientSection 𝓑 q
      ⟨integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j,
        homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p i j⟩ a ha U hU) =
    E (integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential h p) i j)
  have hh : (fun l => (u : Localization t.1.asHomogeneousIdeal.toIdeal.primeCompl) *
      (E ∘ h) l) = A ∘ H := by
    funext l
    exact nativeHomogeneousChartCoefficientSection_spec 𝓑 q ⟨H l,hH l⟩ a ha U hU t
  have hd : (u : Localization t.1.asHomogeneousIdeal.toIdeal.primeCompl) *
      E (integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential h p) i j) =
    A (integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j) := by
    rw [homogeneousKoszulCoordinateDifferential_entry_map E h,
      ← homogeneousKoszulCoordinateDifferential_entry_scale, hh,
      ← homogeneousKoszulCoordinateDifferential_entry_map A H]
  apply (Units.mul_right_inj u).mp
  exact (nativeHomogeneousChartCoefficientSection_spec 𝓑 q
    ⟨integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) i j,
      homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p i j⟩ a ha U hU t).trans hd.symm

/-- The WHOLE SAME ACTUAL original global differential in original integer
frames is the standard exterior Koszul differential for ORIGINAL H_i/a^q,
for every original chart subopen,all degrees and every integer twist. -/
theorem nativeGlobalKoszulDifferential_standardSectionFrame {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (k : ℤ)
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
          (homogeneousKoszulCoordinateDifferential
            (fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU) p v) := by
  rw [nativeGlobalKoszulDifferential_sectionFrame]
  apply congrArg
    (nativeIntegerShiftedFreeSectionFrame 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ))
        k a ha (op U) (fun t => hU t.2))
  funext j
  rw [integerShiftedFreeMap_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [nativeHomogeneousKoszulEntry_dehomogenize]
  exact mul_comm _ _

end LinearStudy
