module
public import Linear.NativeIntegerShiftedFreeBicone
public import Linear.NativeIntegerTwistSectionFrames
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
variable {K S I : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq I] (w : I → ℤ) (k : ℤ)

/-- The constructed biproduct projection is the SAME original coordinate projection. -/
theorem nativeIntegerShiftedFreeBiproductIso_hom_projection [Fintype I] (i : I) :
    (nativeIntegerShiftedFreeBiproductIso 𝓑 w k).hom ≫ biproduct.π _ i =
      nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i := by
  exact biproduct.lift_π _ _

/-- The constructed biproduct inclusion is the SAME original coordinate inclusion. -/
theorem nativeIntegerShiftedFreeBiproductIso_inclusion_inv [Fintype I] (i : I) :
    biproduct.ι _ i ≫ (nativeIntegerShiftedFreeBiproductIso 𝓑 w k).inv =
      nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i := by
  exact biproduct.ι_desc _ _

/-- Every original section is the sum of its actual coordinate components. -/
theorem nativeIntegerShiftedFreeSection_coordinate_total [Fintype I]
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U) :
    (∑ i : I, ((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U)
      (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U) x)) = x := by
  have h := congrArg (fun f =>
    (PresheafOfModules.evaluation _ U).map ((SheafOfModules.forget _).map f))
      (nativeIntegerShiftedFree_coordinate_total 𝓑 w k)
  simp only [Functor.map_sum, CategoryTheory.Functor.map_id] at h
  have hx := congrArg (fun f => f.hom x) h
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply] at hx
  change (∑ i : I, ((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i ≫
    nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U).hom x) = x at hx
  exact hx

/-- Actual original a-coordinate frame for the ENTIRE shifted free section
module,for every integer twist and every original subopen of the chart.
Its maps are constructed from original coordinate maps and original line frames. -/
def nativeIntegerShiftedFreeSectionFrame [Fintype I] (a : S) (ha : a ∈ 𝓑 1)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (I → (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 w)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U where
  toFun v := ∑ i : I, ((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U)
    (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp (v i))
  invFun x i := (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp).symm
    (((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U) x)
  left_inv v := by
    funext i
    apply (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [map_sum]
    trans ((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U)
      (((nativeIntegerShiftedFreeCoordinateInclusion 𝓑 w k i).val.app U)
        (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp (v i)))
    · apply Finset.sum_eq_single i
      · intro j hj hji
        have h := congrArg (fun f => (f.val.app U).hom
          (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w j) U hp (v j)))
          (nativeIntegerShiftedFree_inclusion_projection_ne 𝓑 w k j i hji)
        exact h
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    · have h := congrArg (fun f => (f.val.app U).hom
        (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp (v i)))
        (nativeIntegerShiftedFree_inclusion_projection_self 𝓑 w k i)
      exact h

  right_inv x := by
    simp only [LinearEquiv.apply_symm_apply]
    exact nativeIntegerShiftedFreeSection_coordinate_total 𝓑 w k U x
  map_add' v z := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

/-- Original coordinate extraction in the constructed whole-module frame. -/
theorem nativeIntegerShiftedFreeSectionFrame_projection [Fintype I]
    (a : S) (ha : a ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (v : I → (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) (i : I) :
    ((nativeIntegerShiftedFreeCoordinateProjection 𝓑 w k i).val.app U)
      (nativeIntegerShiftedFreeSectionFrame 𝓑 w k a ha U hp v) =
      nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp (v i) := by
  have h := congrFun ((nativeIntegerShiftedFreeSectionFrame 𝓑 w k a ha U hp).symm_apply_apply v) i
  apply (nativeIntegerTwistSectionFrame 𝓑 a ha (k-w i) U hp).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact h

end LinearStudy
