module
public import Linear.NativeLaurentZeroMonomialAssembly
public import Linear.NativePositiveSectionAddHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every ACTUAL global section of the nonnegative native twist on the
original projective space is the section of an ORIGINAL degree-m
homogeneous polynomial. No global-section comparison is assumed. -/
theorem coordinateNativePositiveTwist_polynomial_sections_surjective
    (j : σ) (m : ℕ) :
    Function.Surjective
      (LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m) := by
  classical
  intro s
  let π := homogeneousProjπ (R := K) (σ := σ)
  let M := coordinateNativeIntegerTwist (K := K) (σ := σ) (m : ℤ)
  let U := coordinateOpenCover (R := K) (σ := σ)
  let A := Scheme.Modules.orderedBaseCechAugmentation π M U
  let E := coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) (m : ℤ) 0
  let x := E.hom.hom (A.hom s)
  have hA : (Scheme.Modules.orderedBaseCechDifferential π M U 0).hom (A.hom s) = 0 := by
    have h := ConcreteCategory.congr_hom
      (Scheme.Modules.orderedBaseCechAugmentation_comp_d π M U) s
    exact h
  have hx : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := K) (σ := σ) (m : ℤ) 0).hom x = 0 := by
    have h := ConcreteCategory.congr_hom
      (coordinateNativeLaurentOrderedCechDifferential_naturality (K := K) (σ := σ)
        (m : ℤ) 0) (A.hom s)
    change (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := K) (σ := σ) (m : ℤ) 0).hom x =
      (coordinateNativeLaurentOrderedCechObjectIso (K := K) (σ := σ) (m : ℤ) 1).hom.hom
        ((Scheme.Modules.orderedBaseCechDifferential π M U 0).hom (A.hom s)) at h
    rw [h,hA,map_zero]
  let T := coordinateHomogeneousLaurentActiveWeights (m : ℤ) 0 x
  have hpos (e : T) : ∀ i, 0 ≤ e.1.1 i :=
    coordinateHomogeneousLaurentZeroCycle_active_nonnegative (R := K) (m : ℤ)
      (Int.natCast_nonneg m) j x hx e.1 e.2
  let ell : T → homogeneousSubmodule σ K m := fun e =>
    ⟨monomial e.1.natExponent
      ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
        ((coordinateHomogeneousLaurentWeightComponent (R := K) (m : ℤ) e.1 0 x).1
          (Scheme.Modules.orderedCechSingleton (ULift.up j)))),
      (mem_homogeneousSubmodule m _).mpr
        (e.1.natExponent_monomial_homogeneous m (hpos e) _)⟩
  let Q : homogeneousSubmodule σ K m := ∑ e : T, ell e
  refine ⟨Q,?_⟩
  have hsum : LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m Q =
      ∑ e : T, LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m
        (ell e) :=
    map_sum (LinearStudy.nativePositiveHomogeneousGlobalSectionAddHom
      (homogeneousSubmodule σ K) m) ell Finset.univ
  have hE : E.hom.hom (A.hom
      (LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m Q)) = x := by
    rw [hsum,map_sum,map_sum]
    calc
      ∑ e : T, E.hom.hom (A.hom
        (LinearStudy.nativePositiveHomogeneousGlobalSection (homogeneousSubmodule σ K) m (ell e))) =
          ∑ e : T, coordinateHomogeneousLaurentWeightInclusion (R := K) (m : ℤ) e.1 0
            (coordinateHomogeneousLaurentWeightComponent (R := K) (m : ℤ) e.1 0 x) := by
        apply Finset.sum_congr rfl
        intro e _
        exact coordinateNativeLaurentZeroCycle_monomial_component m j x hx e.1 (hpos e)
      _ = x := by
        rw [Finset.univ_eq_attach]
        exact (Finset.sum_attach T
          (fun e : HomogeneousLaurentExponent σ (m : ℤ) =>
            coordinateHomogeneousLaurentWeightInclusion (R := K) (m : ℤ) e 0
              (coordinateHomogeneousLaurentWeightComponent (R := K) (m : ℤ) e 0 x))).trans
          (coordinateHomogeneousLaurentActiveWeights_reconstruct (m : ℤ) 0 x)
  apply Scheme.Modules.orderedBaseCechAugmentation_injective π M U
    (by rw [iSup_coordinateOpenCover_eq_top (R := K) (σ := σ)])
  apply (ModuleCat.mono_iff_injective E.hom).mp (inferInstance : Mono E.hom)
  exact hE
end MvPolynomial
