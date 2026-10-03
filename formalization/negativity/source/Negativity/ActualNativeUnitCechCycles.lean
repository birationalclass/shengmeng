module
public import Negativity.ActualNativeUnitCechCoordinates

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section

theorem actualNativeUnitCech_cycle_iff {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 1) :
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).d 1 2 x = 0 ↔
      actualCechBoundary X U (actualNativeUnitCechOneEquiv f U x) = 0 := by
  constructor
  · intro hx
    funext j k l
    rw [← actualNativeUnitCech_boundary, hx]
    simp only [map_zero, Pi.zero_apply]
  · intro hx
    apply (actualNativeUnitCechTwoEquiv f U).injective
    funext j k l
    rw [actualNativeUnitCech_boundary]
    simpa only [map_zero] using congrFun (congrFun (congrFun hx j) k) l

def actualNativeUnitCechCycleEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    ((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).g.hom.ker ≃+
      actualCechCocycles X U where
  toFun a := ⟨actualNativeUnitCechOneEquiv f U a.1,
    (actualNativeUnitCech_cycle_iff f U a.1).mp a.2⟩
  invFun a := ⟨(actualNativeUnitCechOneEquiv f U).symm a.1,
    (actualNativeUnitCech_cycle_iff f U _).mpr (by
      rw [(actualNativeUnitCechOneEquiv f U).apply_symm_apply]
      exact a.2)⟩
  left_inv a := Subtype.ext ((actualNativeUnitCechOneEquiv f U).symm_apply_apply a.1)
  right_inv a := Subtype.ext ((actualNativeUnitCechOneEquiv f U).apply_symm_apply a.1)
  map_add' a b := Subtype.ext (map_add (actualNativeUnitCechOneEquiv f U) a.1 b.1)

theorem actualNativeUnitCechCycleEquiv_boundary {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 0) :
    actualNativeUnitCechCycleEquiv f U
      (((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).moduleCatToCycles x) =
        actualCechCoboundary X U (actualNativeUnitCechZeroEquiv f U x) :=
  Subtype.ext (actualNativeUnitCech_difference f U x)

theorem actualNativeUnitCechCycleEquiv_range {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    (((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).moduleCatToCycles.range.toAddSubgroup).map
      (actualNativeUnitCechCycleEquiv f U).toAddMonoidHom = (actualCechCoboundary X U).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    exact ⟨actualNativeUnitCechZeroEquiv f U x,
      (actualNativeUnitCechCycleEquiv_boundary f U x).symm⟩
  · rintro ⟨x, rfl⟩
    let y := (actualNativeUnitCechZeroEquiv f U).symm x
    refine ⟨((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).moduleCatToCycles y,
      ⟨y, rfl⟩, ?_⟩
    exact (actualNativeUnitCechCycleEquiv_boundary f U y).trans
      (congrArg (actualCechCoboundary X U)
        ((actualNativeUnitCechZeroEquiv f U).apply_symm_apply x))

def actualNativeUnitCechHOneExplicitIso {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).homology 1 ≅
      ((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).homology :=
  ShortComplex.homologyMapIso
    ((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).isoSc' 0 1 2
      (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1))

def actualNativeUnitCechHOneAddEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).homology 1 ≃+
      actualCechHOne X U :=
  (actualNativeUnitCechHOneExplicitIso f U).toLinearEquiv.toAddEquiv.trans
    ((((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.trans
    (QuotientAddGroup.congr _ _ (actualNativeUnitCechCycleEquiv f U)
      (actualNativeUnitCechCycleEquiv_range f U)))

theorem actualNativeUnitCechOneEquiv_smul {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤))
    (x : (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).X 1) :
    actualNativeUnitCechOneEquiv f U (r • x) =
      actualCechScaleOne X U (f.appTop r) (actualNativeUnitCechOneEquiv f U x) := by
  funext j k
  rw [actualNativeUnitCechOneEquiv_coe]
  change _ = actualSectionRestriction X le_top (f.appTop r) *
    actualNativeUnitCechOneEquiv f U x j k
  rw [actualNativeUnitCechOneEquiv_coe]
  let V := U j ⊓ U k
  let t : Fin 2 → ι := ![j,k]
  let h := actualNativeProductOpen_one U t
  let φ := (Scheme.Modules.baseModulePresheaf f (SheafOfModules.unit X.ringCatSheaf)).map (eqToHom h.symm).op
  let p := Pi.π (fun a => actualNativeCechFactor f (SheafOfModules.unit X.ringCatSheaf) U 1 a) t
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let q : Γ(M,V) →ₗ[Γ(X,V)] Γ(X,V) := LinearMap.id
  change q (φ.hom (p.hom (r • x))) =
    actualSectionRestriction X (U := V) le_top (f.appTop r) * q (φ.hom (p.hom x))
  rw [p.hom.map_smul, φ.hom.map_smul]
  exact q.map_smul (actualSectionRestriction X le_top (f.appTop r)) (φ.hom (p.hom x))

#print axioms actualNativeUnitCechHOneAddEquiv
#print axioms actualNativeUnitCechOneEquiv_smul
end
end Negativity
