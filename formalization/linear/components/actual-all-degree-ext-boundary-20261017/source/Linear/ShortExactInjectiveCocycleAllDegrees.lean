module
public import Linear.ShortExactInjectiveExtBoundaryAllDegrees
public import Linear.ShortExactInjectiveCochainLiftAllDegrees
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- In every degree,construct the actual lifts and compute the SAME native Ext
boundary. No lift,class identity,or projective source hypothesis is supplied. -/
theorem shortExactInjectiveCocycle_allDegrees_exists
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (q : ℕ)
    (a : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) I.cochainComplex (q : ℤ)) :
    ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) I.cochainComplex (q : ℤ))
      (c : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) I.cochainComplex ((q+1 : ℕ) : ℤ)),
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp b
        (zero_add (q : ℤ)) = a.val ∧
      δ (q : ℤ) ((q+1 : ℕ) : ℤ) b =
        (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp c.val
          (zero_add ((q+1 : ℕ) : ℤ)) ∧
      Ext.δ hS q (q+1) rfl (I.extEquivCohomologyClass.symm (CohomologyClass.mk a)) =
        (I.extEquivCohomologyClass (n := q+1)).symm (CohomologyClass.mk c) := by
  have lift := shortExactInjectiveCochainLift_allDegrees_exists S hS I.cochainComplex
    (q : ℤ) a
  obtain ⟨b,c,hb,hc⟩ := lift
  exact ⟨b,c,hb,hc,shortExactInjectiveExtBoundary_allDegrees S hS I q a b c hb hc⟩

end LinearStudy
