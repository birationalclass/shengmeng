module
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Localization
open CochainComplex.HomComplex
universe u v d
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- Into a K-injective target,every actual derived map has an actual cocycle
representative. Reuse the native K-injective equivalence. -/
theorem cochainKInjectiveDerivedCocycle_exists
    (K L : CochainComplex A ℤ) (q : ℤ) [L.IsKInjective]
    (f : ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) q) :
    ∃ c : Cocycle K L q,
      ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q = f := by
  haveI : HasSmallLocalizedShiftedHom.{d}
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ℤ K L := fun _ _ =>
    hasSmallLocalizedHom_of_isLocalization _ DerivedCategory.Q
  let e := (CohomologyClass.equivOfIsKInjective.{d} (K := K) (L := L) (n := q)).trans
    (SmallShiftedHom.equiv _ DerivedCategory.Q)
  obtain ⟨x,hx⟩ := e.surjective f
  obtain ⟨c,rfl⟩ := x.mk_surjective
  refine ⟨c,?_⟩
  simpa only [e,Equiv.trans_apply,CohomologyClass.equivOfIsKInjective_apply,
    CohomologyClass.equiv_toSmallShiftedHom_mk] using hx

/-- For a K-injective target,derived equality is EXACTLY actual cocycle
cohomology equality;not merely a one-way implication. -/
theorem cochainKInjectiveClassEq_iff_derivedMapEq
    {K L : CochainComplex A ℤ} (q : ℤ) [L.IsKInjective]
    (a b : Cocycle K L q) :
    CohomologyClass.mk a = CohomologyClass.mk b ↔
      ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q =
        ShiftedHom.map (Cocycle.equivHomShift.symm b) DerivedCategory.Q := by
  haveI : HasSmallLocalizedShiftedHom.{d}
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ℤ K L := fun _ _ =>
    hasSmallLocalizedHom_of_isLocalization _ DerivedCategory.Q
  let e := (CohomologyClass.equivOfIsKInjective.{d} (K := K) (L := L) (n := q)).trans
    (SmallShiftedHom.equiv _ DerivedCategory.Q)
  simpa only [e,Equiv.trans_apply,CohomologyClass.equivOfIsKInjective_apply,
    CohomologyClass.equiv_toSmallShiftedHom_mk] using
      (e.injective.eq_iff (a := CohomologyClass.mk a) (b := CohomologyClass.mk b)).symm

end LinearStudy
