module
public import Linear.OriginalChainDegreeOneConeQuasiIso
public import Linear.OriginalChainDegreeOneConeTopCocycle
public import Linear.CochainResolutionSourceQuasiIso
public import Linear.CochainResolutionExtClassAdditive
public import Linear.CochainResolutionExtClassCongruence
public import Linear.ChainResolutionTopExtClass
public import Linear.CochainShortExactRoofClass
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

/-- Compute the SAME original degree-one class,with its actual categorical
quotient augmentation and ordered identity top functional. The native roof
has the opposite sign. No comparison map,square or class identity is assumed. -/
theorem originalChainDegreeOneTopExtClass_eq_neg_roof
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0)
    (he : ∀ p : ℕ,0 < p → C.ExactAt p) :
    letI := originalChainCokernelAugmentation_quasiIso C he
    originalChainTopExtClass C 1 (originalChainCokernelAugmentation C)
      (𝟙 (C.X 1)) (by simp [h]) =
      -cochainShortExactRoofClass (originalChainFirstCokernelSequence C)
        (originalChainFirstCokernelSequence_shortExact C h (he 1 (by omega))) := by
  letI := originalChainCokernelAugmentation_quasiIso C he
  letI := originalChainAugmentationAsCochain_quasiIso C (originalChainCokernelAugmentation C)
  letI := originalChainDegreeOneConeMap_quasiIso C h he
  let S := originalChainFirstCokernelSequence C
  let hs := originalChainFirstCokernelSequence_shortExact C h (he 1 (by omega))
  let T := S.map (CochainComplex.singleFunctor A 0)
  letI := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hs.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
  have ht := cochainResolutionExtClass_sourceQuasiIso
    (originalChainAsCochain C) (CochainComplex.mappingCone T.f)
    (originalChainDegreeOneConeMap C h) 1
    (CochainComplex.mappingCone.descShortComplex T)
    (CochainComplex.mappingCone.triangle T.f).mor₃
  simp only [ShiftedHom.mk₀_comp] at ht
  have hc := cochainResolutionExtClass_congr (originalChainAsCochain C) 1
    (originalChainDegreeOneConeMap C h ≫ CochainComplex.mappingCone.descShortComplex T)
    (originalChainAugmentationAsCochain C (originalChainCokernelAugmentation C))
    (originalChainDegreeOneConeMap_augmentation C h)
    (originalChainDegreeOneConeMap C h ≫ (CochainComplex.mappingCone.triangle T.f).mor₃)
    _ (originalChainDegreeOneConeMap_triangleTop C h)
  rw [cochainResolutionExtClass_neg] at hc
  have ht' := hc.symm.trans ht
  simpa only [originalChainTopExtClass,cochainResolutionTopExtClass,Category.comp_id,
    Nat.cast_one,Int.cast_ofNat_Int,cochainShortExactRoofClass,S,T,hs,
    originalChainFirstCokernelSequence,ShortComplex.map,Cocycle.toSingleMk,
    show (-1:ℤ)-1 = -2 by norm_num] using
      (neg_eq_iff_eq_neg.mp ht')

end LinearStudy
