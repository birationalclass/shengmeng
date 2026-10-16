module
public import Linear.NativeIntegerFreeSpecChartFrames
public import Linear.KoszulCoordinateWholeNaturality
public import Linear.NativeKoszulChartCoefficientSpec
public import Linear.NativeGlobalKoszulDehomogenizedDifferential
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- EVERY actual original Spec-global-section Koszul differential is the
SAME standard Koszul differential of the ORIGINAL away-ring H_i/a^q.
All component maps are the original integer chart frames. -/
theorem nativeProjectiveKoszulSpecDifferential {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1)
    (v : Set.powersetCard (Fin r) (p+1) → HomogeneousLocalization.Away 𝓑 a) :
    let j := Proj.awayι 𝓑 a ha one_pos
    (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor j).map
      (nativeProjectiveKoszulDifferential 𝓑 H hH p k))).hom
        (nativeIntegerShiftedFreeSpecChartFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) (p+1) => ((p+1:ℕ):ℤ)*(q:ℤ))
            k a ha v) =
    nativeIntegerShiftedFreeSpecChartFrame 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k a ha
        (homogeneousKoszulCoordinateDifferential
          (fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
            (by simpa using hH i)) p v) := by
  dsimp only
  rw [nativeIntegerShiftedFreeSpecChartFrame_apply]
  erw [schemeModuleSpecChartSectionsLinearEquiv_naturality]
  rw [nativeIntegerShiftedFreeSpecChartFrame_apply]
  apply congrArg
  erw [nativeGlobalKoszulDifferential_standardSectionFrame 𝓑 H hH p k a ha
    (Proj.basicOpen 𝓑 a) le_rfl]
  apply congrArg
  have hh :
      (fun i => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H i,hH i⟩
        a ha (Proj.basicOpen 𝓑 a) le_rfl) =
      (Proj.awayToSection 𝓑 a).hom ∘
        (fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
          (by simpa using hH i)) := by
    funext i
    exact nativeHomogeneousChartCoefficientSection_full 𝓑 q ⟨H i,hH i⟩ a ha
  rw [hh]
  exact (homogeneousKoszulCoordinateDifferential_map (Proj.awayToSection 𝓑 a).hom
    (fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)) p v).symm

end LinearStudy
