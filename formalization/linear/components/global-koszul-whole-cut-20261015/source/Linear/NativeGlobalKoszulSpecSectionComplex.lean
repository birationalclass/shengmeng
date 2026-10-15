module
public import Linear.NativeGlobalKoszulSpecDifferential
public import Linear.NativeGlobalKoszulAffineCounit
public import Linear.HomogeneousKoszulCoordinateComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- ENTIRE SAME actual original affine-restricted GLOBAL Koszul complex,
after actual Spec global sections,is isomorphic to the SAME standard
coordinate Koszul over the ORIGINAL away ring. EVERY actual differential
commutes,ALL integer twists retained;no desired comparison certificate. -/
def nativeProjectiveKoszulSpecSectionComplexIso {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    letI := affineModuleSpecGlobalSections_additive R
    let j := Proj.awayι 𝓑 a ha one_pos
    ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (nativeProjectiveKoszulOnAffine 𝓑 R j H hH k) ≅
    homogeneousKoszulCoordinateComplex
      (fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
        (by simpa using hH i)) :=
by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  letI := affineModuleSpecGlobalSections_additive R
  exact HomologicalComplex.Hom.isoOfComponents
    (fun p => (nativeIntegerShiftedFreeSpecChartFrame 𝓑
      (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k a ha).symm.toModuleIso) (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      subst hij
      simp only [Functor.mapHomologicalComplex_obj_d,nativeProjectiveKoszulOnAffine,
        nativeProjectiveKoszulComplex,homogeneousKoszulCoordinateComplex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      symm
      change ((nativeIntegerShiftedFreeSpecChartFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) j => (j:ℤ)*(q:ℤ)) k a ha).symm.toLinearMap).comp
        (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor
          (Proj.awayι 𝓑 a ha one_pos)).map
            (nativeProjectiveKoszulDifferential 𝓑 H hH j k))).hom =
        (homogeneousKoszulCoordinateDifferential
          (fun l => HomogeneousLocalization.Away.mk 𝓑 ha q (H l)
            (by simpa using hH l)) j).comp
          (nativeIntegerShiftedFreeSpecChartFrame 𝓑
            (fun _ : Set.powersetCard (Fin r) (j+1) => ((j+1:ℕ):ℤ)*(q:ℤ)) k a ha).symm.toLinearMap
      apply LinearMap.ext
      intro x
      change (nativeIntegerShiftedFreeSpecChartFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) j => (j:ℤ)*(q:ℤ)) k a ha).symm
        ((moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor
          (Proj.awayι 𝓑 a ha one_pos)).map
            (nativeProjectiveKoszulDifferential 𝓑 H hH j k))).hom x) =
        homogeneousKoszulCoordinateDifferential
          (fun l => HomogeneousLocalization.Away.mk 𝓑 ha q (H l)
            (by simpa using hH l)) j
          ((nativeIntegerShiftedFreeSpecChartFrame 𝓑
            (fun _ : Set.powersetCard (Fin r) (j+1) => ((j+1:ℕ):ℤ)*(q:ℤ)) k a ha).symm x)
      apply (nativeIntegerShiftedFreeSpecChartFrame 𝓑
        (fun _ : Set.powersetCard (Fin r) j => (j:ℤ)*(q:ℤ)) k a ha).injective
      rw [LinearEquiv.apply_symm_apply]
      have hd := nativeProjectiveKoszulSpecDifferential 𝓑 H hH j k a ha
        ((nativeIntegerShiftedFreeSpecChartFrame 𝓑
          (fun _ : Set.powersetCard (Fin r) (j+1) => ((j+1:ℕ):ℤ)*(q:ℤ)) k a ha).symm x)
      rw [LinearEquiv.apply_symm_apply] at hd
      exact hd)

/-- EVERY comparison component is the SAME original Spec frame inverse. -/
theorem nativeProjectiveKoszulSpecSectionComplexIso_hom {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (p : ℕ) :
    (nativeProjectiveKoszulSpecSectionComplexIso 𝓑 H hH k a ha).hom.f p =
      ModuleCat.ofHom (nativeIntegerShiftedFreeSpecChartFrame 𝓑
        (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) k a ha).symm.toLinearMap := rfl

end LinearStudy
