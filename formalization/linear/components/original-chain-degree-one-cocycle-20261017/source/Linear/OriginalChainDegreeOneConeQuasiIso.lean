module
public import Linear.OriginalChainDegreeOneConeAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Derive the ACTUAL first quotient sequence's short exactness from the
original degree-one exactness and the vanishing actual incoming differential. -/
theorem originalChainFirstCokernelSequence_shortExact
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0) (he : C.ExactAt 1) :
    (originalChainFirstCokernelSequence C).ShortExact := by
  have he' := (C.exactAt_iff' 2 1 0 (by simp) (by simp)).mp he
  haveI : Mono (C.d 1 0) := ((C.sc' 2 1 0).exact_iff_mono h).mp he'
  change (ShortComplex.mk (C.d 1 0) (cokernel.π (C.d 1 0)) _).ShortExact
  refine { exact := ?_,mono_f := inferInstance,epi_g := inferInstance }
  exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (C.d 1 0))

/-- The constructed chain-to-cone comparison is a quasi-isomorphism,derived
from original positive exactness and the PROVED SAME augmentation square. -/
theorem originalChainDegreeOneConeMap_quasiIso
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0)
    (he : ∀ p : ℕ,0 < p → C.ExactAt p) :
    QuasiIso (originalChainDegreeOneConeMap C h) := by
  have hs := originalChainFirstCokernelSequence_shortExact C h (he 1 (by omega))
  let T := (originalChainFirstCokernelSequence C).map (CochainComplex.singleFunctor A 0)
  letI := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hs.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
  letI := originalChainCokernelAugmentation_quasiIso C he
  letI := originalChainAugmentationAsCochain_quasiIso C (originalChainCokernelAugmentation C)
  haveI : QuasiIso (originalChainDegreeOneConeMap C h ≫
      CochainComplex.mappingCone.descShortComplex T) := by
    rw [originalChainDegreeOneConeMap_augmentation]
    infer_instance
  exact quasiIso_of_comp_right (originalChainDegreeOneConeMap C h)
    (CochainComplex.mappingCone.descShortComplex T)

end LinearStudy
