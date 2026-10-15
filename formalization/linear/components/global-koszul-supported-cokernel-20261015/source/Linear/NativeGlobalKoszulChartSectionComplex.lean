module
public import Linear.NativeGlobalKoszulDehomogenizedDifferential
public import Linear.HomogeneousKoszulCoordinateComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The ENTIRE SAME ORIGINAL GLOBAL Koszul complex evaluated on ANY
original a-chart subopen is chain-isomorphic to the standard ORIGINAL
dehomogenized Koszul coordinate complex,at EVERY integer twist.
All components are the original section frames;EVERY differential commutes. -/
def nativeGlobalKoszulChartSectionComplexIso {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) :
    ((SheafOfModules.forget (Proj 𝓑).ringCatSheaf ⋙
      PresheafOfModules.evaluation (Proj 𝓑).ringCatSheaf.obj (op U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (nativeProjectiveKoszulComplex 𝓑 H hH k) ≅
    homogeneousKoszulCoordinateComplex (S := (Proj 𝓑).presheaf.obj (op U))
      (fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (nativeIntegerShiftedFreeSectionFrame 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ))
        k a ha (op U) (fun t => hU t.2)).symm.toModuleIso) (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      subst hij
      simp only [Functor.mapHomologicalComplex_obj_d, nativeProjectiveKoszulComplex,
        homogeneousKoszulCoordinateComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      symm
      change ((nativeIntegerShiftedFreeSectionFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) j => (j:ℤ)*(q:ℤ))
            k a ha (op U) (fun t => hU t.2)).symm.toLinearMap).comp
        ((nativeProjectiveKoszulDifferential 𝓑 H hH j k).val.app (op U)).hom =
        (homogeneousKoszulCoordinateDifferential
          (fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU) j).comp
            (nativeIntegerShiftedFreeSectionFrame 𝓑
              (fun _ : Set.powersetCard (Fin r) (j+1) => ((j+1:ℕ):ℤ)*(q:ℤ))
                k a ha (op U) (fun t => hU t.2)).symm.toLinearMap
      apply LinearMap.ext
      intro x
      change (nativeIntegerShiftedFreeSectionFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) j => (j:ℤ)*(q:ℤ))
            k a ha (op U) (fun t => hU t.2)).symm
        (((nativeProjectiveKoszulDifferential 𝓑 H hH j k).val.app (op U)) x) =
        homogeneousKoszulCoordinateDifferential
          (fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU) j
            ((nativeIntegerShiftedFreeSectionFrame 𝓑
              (fun _ : Set.powersetCard (Fin r) (j+1) => ((j+1:ℕ):ℤ)*(q:ℤ))
                k a ha (op U) (fun t => hU t.2)).symm x)
      apply (nativeIntegerShiftedFreeSectionFrame 𝓑
        (fun _ : Set.powersetCard (Fin r) j => (j:ℤ)*(q:ℤ))
          k a ha (op U) (fun t => hU t.2)).injective
      rw [LinearEquiv.apply_symm_apply]
      have hd := nativeGlobalKoszulDifferential_standardSectionFrame 𝓑 H hH j k a ha U hU
        ((nativeIntegerShiftedFreeSectionFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) (j+1) => ((j+1:ℕ):ℤ)*(q:ℤ))
            k a ha (op U) (fun t => hU t.2)).symm x)
      rw [LinearEquiv.apply_symm_apply] at hd
      exact hd)

/-- Every component of the ACTUAL complex comparison is the SAME original frame inverse. -/
theorem nativeGlobalKoszulChartSectionComplexIso_hom {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (p : ℕ) :
    (nativeGlobalKoszulChartSectionComplexIso 𝓑 H hH k a ha U hU).hom.f p =
      ModuleCat.ofHom (nativeIntegerShiftedFreeSectionFrame 𝓑
        (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ))
          k a ha (op U) (fun t => hU t.2)).symm.toLinearMap := rfl

end LinearStudy
