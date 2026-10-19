module
public import Linear.CochainKInjectiveDerivedCocycle
public import Linear.CochainResolutionExtClass
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- Starting with the ACTUAL augmentation and cocycle,construct an injective
cocycle representing the SAME roof and PROVE the actual pullback class equation.
No representative or class-identity premise is supplied. -/
theorem cochainResolutionInjectiveCocycle_exists
    (K : CochainComplex A ℤ) {E N : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : Cocycle K ((CochainComplex.singleFunctor A 0).obj N) (r : ℤ))
    (I : InjectiveResolution N) :
    ∃ c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) I.cochainComplex (r : ℤ),
      CohomologyClass.mk (c.precomp alpha) = CohomologyClass.mk (beta.postcomp I.ι') ∧
      cochainResolutionExtClass K r alpha (Cocycle.equivHomShift.symm beta) =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c) := by
  obtain ⟨c,hc⟩ := cochainKInjectiveDerivedCocycle_exists
    ((CochainComplex.singleFunctor A 0).obj E) I.cochainComplex (r : ℤ)
    (inv (DerivedCategory.Q.map alpha) ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm (beta.postcomp I.ι')) DerivedCategory.Q)
  refine ⟨c,?_,?_⟩
  · apply (cochainKInjectiveClassEq_iff_derivedMapEq (r : ℤ) _ _).mpr
    simp only [Cocycle.equivHomShift_symm_precomp,ShiftedHom.map,
      CategoryTheory.Functor.map_comp,Category.assoc] at hc ⊢
    rw [hc]
    simp only [IsIso.hom_inv_id_assoc]
  · apply Ext.ext
    rw [cochainResolutionExtClass_hom,I.extEquivCohomologyClass_symm_mk_hom]
    simp only [DerivedCategory.singleFunctorIsoCompQ_hom_app,
      DerivedCategory.singleFunctorIsoCompQ_inv_app,ShiftedHom.mk₀_comp,
      ShiftedHom.comp_mk₀,Category.id_comp,Category.comp_id,
      CategoryTheory.Functor.map_id]
    rw [hc]
    simp only [Cocycle.equivHomShift_symm_postcomp,ShiftedHom.map,
      CategoryTheory.Functor.map_comp,Category.assoc]
    erw [(Functor.commShiftIso DerivedCategory.Q (r : ℤ)).hom.naturality_assoc I.ι']
    simp only [CategoryTheory.Functor.comp_map,Category.assoc,← CategoryTheory.Functor.map_comp,
      IsIso.hom_inv_id,IsIso.hom_inv_id_assoc,CategoryTheory.Functor.map_id,Category.comp_id]

end LinearStudy
