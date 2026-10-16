module
public import Linear.ShortExactRoofInjectiveCocycle
public import Linear.ShortExactInjectiveCochainLift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- EVERY actual short-exact roof and ANY coefficient injective resolution have
CONSTRUCTED cochain lift data. The SAME actual class and native degree-zero
source boundary are computed on that SAME cocycle. No lift or class-identity
premise remains. This is the degree-one building block,not the arbitrary-r
original Koszul epsilon formula. -/
theorem shortExactInjectiveCocycleRealization
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (a : S.X₁ ⟶ N) :
    ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) I.cochainComplex 0)
      (c : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) I.cochainComplex 1),
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp b (zero_add 0) =
        Cochain.ofHom ((CochainComplex.singleFunctor A 0).map a ≫ I.ι') ∧
      δ 0 1 b = (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp c.val
        (zero_add 1) ∧
      (cochainShortExactRoofClass S hS).comp (Ext.mk₀ a) (add_zero 1) =
        -(I.extEquivCohomologyClass.symm (CohomologyClass.mk c)) ∧
      Ext.δ hS 0 1 rfl (Ext.mk₀ a) =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c) := by
  obtain ⟨b,c,hb,hc⟩ := shortExactInjectiveCochainLift_exists S hS I.cochainComplex
    ((CochainComplex.singleFunctor A 0).map a ≫ I.ι')
  have hclass := shortExactRoof_comp_eq_neg_injectiveCocycle S hS I a b c hb hc
  refine ⟨b,c,hb,hc,hclass,?_⟩
  rw [cochainShortExactRoofClass_contravariant_zero_sign,hclass,neg_neg]

end LinearStudy
