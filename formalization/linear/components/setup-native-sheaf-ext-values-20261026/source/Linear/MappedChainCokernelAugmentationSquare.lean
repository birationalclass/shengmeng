module
public import Linear.OriginalChainMappedAugmentationComparison
public import Linear.ChainActualCokernelTargetAugmentation
public import Linear.MappedChainCokernelPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- The ACTUAL augmentation determined by a specified original quotient
cofork. Its map is the cofork projection,not a free augmentation. -/
def originalChainCoforkAugmentation (D : ChainComplex B ℕ)
    (Q : CokernelCofork (D.d 1 0)) : D ⟶ (ChainComplex.single₀ B).obj Q.pt :=
  (ChainComplex.toSingle₀Equiv D _).symm ⟨Q.π,Q.condition⟩

/-- Actual target comparison constructed from mapped-cokernel
preservation and the SAME whole-complex iso and quotient cofork.
The original application constructs these actual data. -/
def mappedOriginalChainTargetCokernelChartIso
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q)
    (T : A) (ec : cokernel (C.d 1 0) ≅ T) : F.obj T ≅ Q.pt :=
  (F.mapIso ec).symm ≪≫ mappedChainFirstCokernelPresentationIso F C D gamma Q hQ

/-- The zero component of the ACTUAL mapped augmentation is the actual
functor image of its original zero component;single comparisons remain. -/
theorem mappedOriginalChainAugmentation_f_zero
    (F : A ⥤ B) [F.Additive] (C : ChainComplex A ℕ) {E : A}
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) :
    (mappedOriginalChainAugmentation F C alpha).f 0 = F.map (alpha.f 0) := by
  simp [mappedOriginalChainAugmentation,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]

/-- PROVE the WHOLE actual chain-augmentation square from the original
cokernel projection identity. No desired augmentation or Ext equality is
assumed. This is the generic boundary for the actual original chart. -/
theorem mappedOriginalChainCokernelTargetAugmentation_chart_comm
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q)
    (T : A) (ec : cokernel (C.d 1 0) ≅ T) :
    mappedOriginalChainAugmentation F C (originalChainCokernelTargetAugmentation C T ec) ≫
        (ChainComplex.single₀ B).map (mappedOriginalChainTargetCokernelChartIso F C D gamma Q hQ T ec).hom =
      gamma.hom ≫ originalChainCoforkAugmentation D Q := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,ChainComplex.single₀_map_f_zero,
    mappedOriginalChainAugmentation_f_zero,originalChainCokernelTargetAugmentation_f_zero,
    originalChainCoforkAugmentation,ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    mappedOriginalChainTargetCokernelChartIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv]
  simp only [Functor.map_comp,Category.assoc]
  erw [← F.map_comp_assoc ec.hom ec.inv,Iso.hom_inv_id,F.map_id,Category.id_comp]
  exact mappedChainFirstCokernelPresentationIso_projection F C D gamma Q hQ

end LinearStudy
