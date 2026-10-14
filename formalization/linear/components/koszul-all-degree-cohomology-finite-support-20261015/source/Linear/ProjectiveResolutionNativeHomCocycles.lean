module
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R] {X : ModuleCat.{u} R}

/-- An ACTUAL native Hom-complex cycle is an ACTUAL cocycle on SAME
original projective resolution. Native linearYonedaObj only is reused. -/
theorem projectiveResolutionNativeHomCycle_isCocycle
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (j : ℕ)
    (z : LinearMap.ker ((P.complex.linearYonedaObj R N).d j (j+1)).hom) :
    P.complex.d (j+1) j ≫ z.val = 0 := z.property

/-- ACTUAL native original Hom cycles map linearly to ACTUAL DERIVED
MODULE Ext using SAME projective resolution's native extMk. N arbitrary;
no desired comparison or coefficient FP/free/flat/invertibility/CM input. -/
def projectiveResolutionNativeHomCycleExtLinearMap
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (j : ℕ) :
    LinearMap.ker ((P.complex.linearYonedaObj R N).d j (j+1)).hom →ₗ[R]
      CategoryTheory.Abelian.Ext.{u} X N j where
  toFun z := P.extMk z.val (j+1) rfl
    (projectiveResolutionNativeHomCycle_isCocycle P N j z)
  map_add' z w :=
    (P.add_extMk z.val w.val (j+1) rfl
      (projectiveResolutionNativeHomCycle_isCocycle P N j z)
      (projectiveResolutionNativeHomCycle_isCocycle P N j w)).symm
  map_smul' a z := by
    have hp := P.extMk_comp_mk₀ z.val (j+1) rfl
      (projectiveResolutionNativeHomCycle_isCocycle P N j z) (a • 𝟙 N)
    have hs : z.val ≫ (a • 𝟙 N) = (a • z).val := by
      rw [Linear.comp_smul,Category.comp_id]
      rfl
    have hp' : (P.extMk z.val (j+1) rfl
        (projectiveResolutionNativeHomCycle_isCocycle P N j z)).comp
        (Ext.mk₀ (a • 𝟙 N)) (add_zero _) =
      P.extMk (a • z).val (j+1) rfl
        (projectiveResolutionNativeHomCycle_isCocycle P N j (a • z)) := by
      simpa only [hs] using hp
    exact hp'.symm.trans (CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀ _ a).symm

/-- Every ACTUAL derived MODULE Ext degree has a SAME original native
Hom-complex cycle representative. No generic Ext-comparison premise. -/
theorem projectiveResolutionNativeHomCycleExtLinearMap_surjective
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (j : ℕ) :
    Function.Surjective (projectiveResolutionNativeHomCycleExtLinearMap P N j) := by
  intro e
  obtain ⟨f,hf,he⟩ := P.extMk_surjective e (j+1) rfl
  refine ⟨⟨f,hf⟩,he⟩

/-- In each positive degree,the ACTUAL native cycle Ext-map kernel is
EXACTLY SAME original native boundary image. This will construct the
actual cohomology comparison,without assuming a desired isomorphism. -/
theorem projectiveResolutionNativeHomCycleExtLinearMap_kernel
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) (n : ℕ) :
    LinearMap.ker (projectiveResolutionNativeHomCycleExtLinearMap P N (n+1)) =
      LinearMap.range ((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2)).moduleCatToCycles := by
  apply Submodule.ext
  intro z
  change P.extMk z.val (n+2) rfl
      (projectiveResolutionNativeHomCycle_isCocycle P N (n+1) z) = 0 ↔
    ∃ F, ((P.complex.linearYonedaObj R N).sc' n (n+1) (n+2)).moduleCatToCycles F = z
  rw [P.extMk_eq_zero_iff z.val (n+2) rfl
    (projectiveResolutionNativeHomCycle_isCocycle P N (n+1) z) n rfl]
  constructor
  · rintro ⟨F,hF⟩
    refine ⟨F,?_⟩
    apply Subtype.ext
    exact hF
  · rintro ⟨F,hF⟩
    exact ⟨F,congrArg Subtype.val hF⟩

end LinearStudy
