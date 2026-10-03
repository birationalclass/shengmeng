module
public import Negativity.ActualNativeCechKernelComparison
public import Negativity.ActualCechCohomologyExact

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

def actualNativeUnitCechZeroEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 0 ≃+
      actualCechZero X U :=
  (actualNativeCechXIsoPi f (SheafOfModules.unit X.ringCatSheaf) U 0).toLinearEquiv.toAddEquiv
    |>.trans (actualModuleCechZeroEquiv (SheafOfModules.unit X.ringCatSheaf) U)

def actualNativeUnitCechOneEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 1 ≃+
      actualCechOne X U :=
  (actualNativeCechXIsoPi f (SheafOfModules.unit X.ringCatSheaf) U 1).toLinearEquiv.toAddEquiv
    |>.trans (actualModuleCechOneEquiv (SheafOfModules.unit X.ringCatSheaf) U)

def actualNativeUnitCechTwoEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 2 ≃+
      actualCechTwo X U :=
  (actualNativeCechXIsoPi f (SheafOfModules.unit X.ringCatSheaf) U 2).toLinearEquiv.toAddEquiv
    |>.trans (actualModuleCechTwoEquiv (SheafOfModules.unit X.ringCatSheaf) U)

theorem actualNativeUnitCechZeroEquiv_coe {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 0)
    (j : ι) :
    actualNativeUnitCechZeroEquiv f U x j =
      actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf)
        (actualNativeProductOpen_zero U ![j])
        ((Pi.π (fun t => actualNativeCechFactor f
          (SheafOfModules.unit X.ringCatSheaf) U 0 t) ![j]).hom x) := by
  rfl

theorem actualNativeUnitCechOneEquiv_coe {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 1)
    (j k : ι) :
    actualNativeUnitCechOneEquiv f U x j k =
      actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf)
        (actualNativeProductOpen_one U ![j,k])
        ((Pi.π (fun t => actualNativeCechFactor f
          (SheafOfModules.unit X.ringCatSheaf) U 1 t) ![j,k]).hom x) := by
  rfl

theorem actualNativeUnitCechTwoEquiv_coe {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 2)
    (j k l : ι) :
    actualNativeUnitCechTwoEquiv f U x j k l =
      actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf)
        (actualNativeProductOpen_two U ![j,k,l])
        ((Pi.π (fun t => actualNativeCechFactor f
          (SheafOfModules.unit X.ringCatSheaf) U 2 t) ![j,k,l]).hom x) := by
  rfl

theorem actualNativeUnitCechZeroEquiv_coe_tuple {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 0)
    (t : Fin 1 → ι) :
    actualNativeUnitCechZeroEquiv f U x (t 0) =
      actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf)
        (actualNativeProductOpen_zero U t)
        ((Pi.π (fun a => actualNativeCechFactor f
          (SheafOfModules.unit X.ringCatSheaf) U 0 a) t).hom x) := by
  have ht : ![t 0] = t := by funext a; fin_cases a; rfl
  rw [← ht]
  exact actualNativeUnitCechZeroEquiv_coe f U x (t 0)

theorem actualNativeUnitCechOneEquiv_coe_tuple {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 1)
    (t : Fin 2 → ι) :
    actualNativeUnitCechOneEquiv f U x (t 0) (t 1) =
      actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf)
        (actualNativeProductOpen_one U t)
        ((Pi.π (fun a => actualNativeCechFactor f
          (SheafOfModules.unit X.ringCatSheaf) U 1 a) t).hom x) := by
  have ht : ![t 0,t 1] = t := by funext a; fin_cases a <;> rfl
  rw [← ht]
  exact actualNativeUnitCechOneEquiv_coe f U x (t 0) (t 1)

theorem actualUnitModuleTransportRestriction {X : Scheme.{u}}
    {V V' W W' : X.Opens} (hV : V = V') (hW : W = W')
    (h : V ≤ W) (h' : V' ≤ W') (x : Γ(X,W)) :
    actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf) hV
        ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE h).op x) =
      actualSectionRestriction X h'
        (actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf) hW x) := by
  subst V'; subst W'
  simp only [actualModuleSectionTransport, eqToIso_refl, Iso.op_refl, Functor.mapIso_refl]
  rfl

theorem actualNativeUnitCech_difference {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f ((SheafOfModules.unit X.ringCatSheaf)) U).X 0) :
    (actualNativeUnitCechOneEquiv f U
      ((Scheme.Modules.baseCechComplex f ((SheafOfModules.unit X.ringCatSheaf)) U).d 0 1 x)) =
        actualCechDifference X U (actualNativeUnitCechZeroEquiv f U x) := by
  funext j k
  let M := (SheafOfModules.unit X.ringCatSheaf)
  let t : Fin 2 → ι := ![j,k]
  have hd := ConcreteCategory.congr_hom
    (actualNativeCech_d_comp_projection f M U 0 t) x
  change (Pi.π (fun a => actualNativeCechFactor f M U 1 a) t).hom
      ((Scheme.Modules.baseCechComplex f M U).d 0 1 x) =
    ∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
      ((Scheme.Modules.baseModulePresheaf f M).map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ a).toOrderHom.toFun).φ t).op).hom
        ((Pi.π (fun a => actualNativeCechFactor f M U 0 a)
          (t ∘ (SimplexCategory.δ a).toOrderHom.toFun)).hom x) at hd
  rw [Fin.sum_univ_two] at hd
  norm_num at hd
  rw [← sub_eq_add_neg] at hd
  rw [actualNativeUnitCechOneEquiv_coe]
  change _ = actualSectionRestriction X inf_le_right
      ((actualNativeUnitCechZeroEquiv f U x) k) -
    actualSectionRestriction X inf_le_left ((actualNativeUnitCechZeroEquiv f U x) j)
  rw [actualNativeUnitCechZeroEquiv_coe, actualNativeUnitCechZeroEquiv_coe]
  change actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf) (actualNativeProductOpen_one U t) _ = _
  rw [hd, map_sub]
  change _ = actualSectionRestriction X inf_le_right _ -
    actualSectionRestriction X inf_le_left _
  congr 1
  · refine (actualUnitModuleTransportRestriction
      (actualNativeProductOpen_one U t)
      (actualNativeProductOpen_zero U
        (t ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun))
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ t)) inf_le_right
      ((Pi.π (fun a => actualNativeCechFactor f M U 0 a)
        (t ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun)).hom x)).trans ?_
    exact congrArg (actualSectionRestriction X inf_le_right)
      ((actualNativeUnitCechZeroEquiv_coe_tuple f U x
        (t ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun)).symm.trans
          (actualNativeUnitCechZeroEquiv_coe f U x k))
  · refine (actualUnitModuleTransportRestriction
      (actualNativeProductOpen_one U t)
      (actualNativeProductOpen_zero U
        (t ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun))
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ t)) inf_le_left
      ((Pi.π (fun a => actualNativeCechFactor f M U 0 a)
        (t ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).hom x)).trans ?_
    exact congrArg (actualSectionRestriction X inf_le_left)
      ((actualNativeUnitCechZeroEquiv_coe_tuple f U x
        (t ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).symm.trans
          (actualNativeUnitCechZeroEquiv_coe f U x j))

theorem actualNativeUnitCech_boundary {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f ((SheafOfModules.unit X.ringCatSheaf)) U).X 1)
    (j k l : ι) :
    (actualNativeUnitCechTwoEquiv f U
      ((Scheme.Modules.baseCechComplex f ((SheafOfModules.unit X.ringCatSheaf)) U).d 1 2 x) j k l :
        Γ(X, (U j ⊓ U k) ⊓ U l)) =
      actualCechBoundary X U (actualNativeUnitCechOneEquiv f U x) j k l := by
  let M := (SheafOfModules.unit X.ringCatSheaf)
  let t : Fin 3 → ι := ![j,k,l]
  have hd := ConcreteCategory.congr_hom
    (actualNativeCech_d_comp_projection f M U 1 t) x
  change (Pi.π (fun a => actualNativeCechFactor f M U 2 a) t).hom
      ((Scheme.Modules.baseCechComplex f M U).d 1 2 x) =
    ∑ a : Fin 3, (-1 : ℤ) ^ (a : ℕ) •
      ((Scheme.Modules.baseModulePresheaf f M).map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ a).toOrderHom.toFun).φ t).op).hom
        ((Pi.π (fun a => actualNativeCechFactor f M U 1 a)
          (t ∘ (SimplexCategory.δ a).toOrderHom.toFun)).hom x) at hd
  rw [Fin.sum_univ_three] at hd
  norm_num at hd
  rw [← sub_eq_add_neg] at hd
  rw [actualNativeUnitCechTwoEquiv_coe]
  change _ = actualSectionRestriction X _ ((actualNativeUnitCechOneEquiv f U x) k l) -
    actualSectionRestriction X _ ((actualNativeUnitCechOneEquiv f U x) j l) +
    actualSectionRestriction X _ ((actualNativeUnitCechOneEquiv f U x) j k)
  rw [actualNativeUnitCechOneEquiv_coe, actualNativeUnitCechOneEquiv_coe,
    actualNativeUnitCechOneEquiv_coe]
  change actualModuleSectionTransport (SheafOfModules.unit X.ringCatSheaf) (actualNativeProductOpen_two U t) _ = _
  rw [hd, map_add, map_sub]
  congr 1
  · congr 1
    · refine (actualUnitModuleTransportRestriction
        (actualNativeProductOpen_two U t)
        (actualNativeProductOpen_one U
          (t ∘ (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun))
        (leOfHom (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun).φ t))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        ((Pi.π (fun a => actualNativeCechFactor f M U 1 a)
          (t ∘ (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun)).hom x)).trans ?_
      exact congrArg (actualSectionRestriction X
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
        ((actualNativeUnitCechOneEquiv_coe_tuple f U x
          (t ∘ (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun)).symm.trans
            (actualNativeUnitCechOneEquiv_coe f U x k l))
    · refine (actualUnitModuleTransportRestriction
        (actualNativeProductOpen_two U t)
        (actualNativeProductOpen_one U
          (t ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFun))
        (leOfHom (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFun).φ t))
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        ((Pi.π (fun a => actualNativeCechFactor f M U 1 a)
          (t ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFun)).hom x)).trans ?_
      exact congrArg (actualSectionRestriction X
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
        ((actualNativeUnitCechOneEquiv_coe_tuple f U x
          (t ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFun)).symm.trans
            (actualNativeUnitCechOneEquiv_coe f U x j l))
  · refine (actualUnitModuleTransportRestriction
      (actualNativeProductOpen_two U t)
      (actualNativeProductOpen_one U
        (t ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun))
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun).φ t)) inf_le_left
      ((Pi.π (fun a => actualNativeCechFactor f M U 1 a)
        (t ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun)).hom x)).trans ?_
    exact congrArg (actualSectionRestriction X inf_le_left)
      ((actualNativeUnitCechOneEquiv_coe_tuple f U x
        (t ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun)).symm.trans
          (actualNativeUnitCechOneEquiv_coe f U x j k))


#print axioms actualNativeUnitCech_difference
#print axioms actualNativeUnitCech_boundary
end
end Negativity
