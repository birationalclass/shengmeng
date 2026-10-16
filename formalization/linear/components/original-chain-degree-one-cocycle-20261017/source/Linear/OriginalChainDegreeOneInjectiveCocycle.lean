module
public import Linear.OriginalChainDegreeOneBoundaryClass
public import Linear.ShortExactInjectiveCocycleRealization
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

/-- CONSTRUCT a cocycle for the SAME ORIGINAL chain class in degree ONE,
with its SAME quotient augmentation and ANY original top functional a.
No comparison map,lift,augmentation square or class identity is an input.
The arbitrary-r original Koszul epsilon still requires source iteration. -/
theorem originalChainDegreeOneInjectiveCocycleRealization
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0)
    (he : ∀ p : ℕ,0 < p → C.ExactAt p) {N : A} (I : InjectiveResolution N)
    (a : C.X 1 ⟶ N) :
    letI := originalChainCokernelAugmentation_quasiIso C he
    ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj (C.X 0)) I.cochainComplex 0)
      (c : Cocycle ((CochainComplex.singleFunctor A 0).obj (cokernel (C.d 1 0)))
        I.cochainComplex 1),
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map (C.d 1 0))).comp b
        (zero_add 0) = Cochain.ofHom ((CochainComplex.singleFunctor A 0).map a ≫ I.ι') ∧
      δ 0 1 b = (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map
        (cokernel.π (C.d 1 0)))).comp c.val (zero_add 1) ∧
      originalChainTopExtClass C 1 (originalChainCokernelAugmentation C)
        a (by simp [h]) = I.extEquivCohomologyClass.symm (CohomologyClass.mk c) := by
  letI := originalChainCokernelAugmentation_quasiIso C he
  obtain ⟨b,c,hb,hc,_,hd⟩ := shortExactInjectiveCocycleRealization
    (originalChainFirstCokernelSequence C)
    (originalChainFirstCokernelSequence_shortExact C h (he 1 (by omega))) I a
  refine ⟨b,c,hb,hc,?_⟩
  rw [originalChainDegreeOneTopExtClass_eq_boundary C h he a]
  exact hd

end LinearStudy
