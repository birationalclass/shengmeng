module
public import Linear.CochainOpcycleSourceSequence
public import Linear.ShortExactInjectiveBoundaryComponents
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

/-- Actual source lift automatically gives BOTH cocycle equations, then
computes the native boundary for SAME actual opcycle sequence. -/
theorem cochainOpcycleInjectiveBoundary_components
    (K : CochainComplex A ℤ) (p : ℤ) (hK : K.ExactAt p)
    {N : A} (I : InjectiveResolution N) (q : ℕ)
    (b : K.X (p+1) ⟶ I.cochainComplex.X (q : ℤ))
    (c : K.opcycles (p+1) ⟶ I.cochainComplex.X ((q+1 : ℕ) : ℤ))
    (hbc : b ≫ I.cochainComplex.d (q : ℤ) ((q+1 : ℕ) : ℤ) = K.pOpcycles (p+1) ≫ c) :
    ∃ (ha : (K.fromOpcycles p (p+1) ≫ b) ≫
        I.cochainComplex.d (q : ℤ) ((q : ℤ)+1) = 0)
      (hc : c ≫ I.cochainComplex.d ((q+1 : ℕ) : ℤ) (((q+1 : ℕ) : ℤ)+1) = 0),
      Ext.δ (cochainOpcycleSourceSequence_shortExact K p hK) q (q+1) rfl
        (I.extEquivCohomologyClass.symm (CohomologyClass.mk
          (Cocycle.fromSingleMk (K.fromOpcycles p (p+1) ≫ b) (zero_add _)
            ((q : ℤ)+1) rfl ha))) =
        (I.extEquivCohomologyClass (n := q+1)).symm (CohomologyClass.mk
          (Cocycle.fromSingleMk c (zero_add _) (((q+1 : ℕ) : ℤ)+1) rfl hc)) := by
  have hq : ((q+1 : ℕ) : ℤ) = (q : ℤ)+1 := by omega
  have ha : (K.fromOpcycles p (p+1) ≫ b) ≫
      I.cochainComplex.d (q : ℤ) ((q : ℤ)+1) = 0 := by
    rw [Category.assoc,← hq,hbc,← Category.assoc]
    simpa only [cochainOpcycleSourceSequence,Category.assoc,zero_comp] using (cochainOpcycleSourceSequence K p).zero_assoc c
  have hc : c ≫ I.cochainComplex.d ((q+1 : ℕ) : ℤ) (((q+1 : ℕ) : ℤ)+1) = 0 := by
    apply (cancel_epi (K.pOpcycles (p+1))).1
    rw [comp_zero,← Category.assoc,← hbc,Category.assoc,
      HomologicalComplex.d_comp_d,comp_zero]
  refine ⟨ha,hc,?_⟩
  exact shortExactInjectiveExtBoundary_components (cochainOpcycleSourceSequence K p)
    (cochainOpcycleSourceSequence_shortExact K p hK) I q _ ha b c hc rfl hbc

end LinearStudy
