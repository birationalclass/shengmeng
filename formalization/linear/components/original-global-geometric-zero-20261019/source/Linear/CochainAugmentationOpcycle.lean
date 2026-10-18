module
public import Linear.CochainOpcycleSourceSequence
public import Linear.CochainResolutionSourceLiftEquations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Canonical degree-zero quotient map induced by the SAME augmentation. -/
def cochainAugmentationOpcycle {K : CochainComplex A ℤ} {E : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) : K.opcycles 0 ⟶ E :=
  HomologicalComplex.opcyclesMap alpha 0 ≫
    (HomologicalComplex.singleObjOpcyclesSelfIso (ComplexShape.up ℤ) 0 E).inv

/-- Its projection is exactly the SAME original augmentation component. -/
theorem cochainAugmentationOpcycle_projection {K : CochainComplex A ℤ} {E : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) :
    K.pOpcycles 0 ≫ cochainAugmentationOpcycle alpha =
      alpha.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom := by
  dsimp only [cochainAugmentationOpcycle]
  rw [← Category.assoc,HomologicalComplex.p_opcyclesMap,Category.assoc,
    HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv]

/-- Quasi-isomorphism and vanishing above degree zero DERIVE the actual
quotient identification,with no separate cokernel-isomorphism input. -/
theorem cochainAugmentationOpcycle_isIso {K : CochainComplex A ℤ} [K.IsStrictlyLE 0]
    {E : A} (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha] :
    IsIso (cochainAugmentationOpcycle alpha) := by
  let L := (CochainComplex.singleFunctor A 0).obj E
  have hK : K.d 0 1 = 0 :=
    (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  haveI := K.isIso_homologyι 0 1 (by simp) hK
  haveI := L.isIso_homologyι 0 1 (by simp) (by simp [L])
  have h := HomologicalComplex.homologyι_naturality alpha 0
  haveI : IsIso (HomologicalComplex.opcyclesMap alpha 0) := by
    have heq : HomologicalComplex.opcyclesMap alpha 0 =
        inv (K.homologyι 0) ≫ HomologicalComplex.homologyMap alpha 0 ≫ L.homologyι 0 := by
      rw [h,IsIso.inv_hom_id_assoc]
    rw [heq]
    infer_instance
  unfold cochainAugmentationOpcycle
  infer_instance

end LinearStudy
