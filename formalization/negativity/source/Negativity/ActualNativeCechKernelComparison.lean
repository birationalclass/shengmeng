module

/-
Copyright (c) 2026 Chris Birkbeck and the negativity formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
The ideal-module kernel identification is adapted from AINTLIB PoleSheaf.lean,
commit 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684, lines 148-164 and 279-315.
Only its categorical kernel construction is reused; no geometric comparison
is assumed as an input.
-/
public import Negativity.ActualCechClosedObstruction
public import Negativity.ActualCechModule
public import Negativity.External.Aintlib.ForMathlib.SchemeModuleBaseCechBasic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
  TopologicalSpace Opposite
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Negativity
noncomputable section

local instance (X : Scheme.{u}) (V : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op V)).Additive where
  map_add := by intro M N f g; rfl

def actualIdealModule {X Z : Scheme.{u}} (i : Z ⟶ X) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

def actualIdealModuleToUnit {X Z : Scheme.{u}} (i : Z ⟶ X) :
    actualIdealModule i ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

def actualIdealModuleAppKernelIso {X Z : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op V)).obj (actualIdealModule i) ≅
      ModuleCat.of Γ(X, V) (RingHom.ker (i.app V).hom) := by
  refine (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op V))
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)).trans
    ((ModuleCat.kernelIsoKer _).trans ?_)
  exact (LinearEquiv.ofEq _ _ (by ext x; rfl)).toModuleIso

@[simp]
theorem actualIdealModuleAppKernelIso_coe {X Z : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (x : Γ(actualIdealModule i, V)) :
    ((actualIdealModuleAppKernelIso i V).hom x : Γ(X, V)) =
      (actualIdealModuleToUnit i).val.app (op V) x := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op V)
  let g := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  have hker : (F.map g).hom.ker = RingHom.ker (i.app V).hom := by
    ext x; rfl
  change ((LinearEquiv.ofEq _ _ hker)
    ((ModuleCat.kernelIsoKer (F.map g)).hom ((PreservesKernel.iso F g).hom x))).1 = _
  refine (LinearEquiv.coe_ofEq_apply hker _).trans ?_
  change (ModuleCat.ofHom (F.map g).hom.ker.subtype)
    (((PreservesKernel.iso F g).hom ≫ (ModuleCat.kernelIsoKer (F.map g)).hom) x) = _
  rw [← ConcreteCategory.comp_apply, Category.assoc,
    ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom,
    kernelComparison_comp_ι]
  rfl

def actualIdealModuleAppKernelAddEquiv {X Z : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) :
    Γ(actualIdealModule i, V) ≃+
      (i.app V).hom.toAddMonoidHom.ker :=
  (actualIdealModuleAppKernelIso i V).toLinearEquiv.toAddEquiv

@[simp]
theorem actualIdealModuleAppKernelAddEquiv_coe {X Z : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (x : Γ(actualIdealModule i, V)) :
    (actualIdealModuleAppKernelAddEquiv i V x : Γ(X, V)) =
      (actualIdealModuleToUnit i).val.app (op V) x :=
  actualIdealModuleAppKernelIso_coe i V x

theorem actualIdealModuleAppKernelAddEquiv_naturality {X Z : Scheme.{u}}
    (i : Z ⟶ X) {V W : X.Opens} (h : V ≤ W)
    (x : Γ(actualIdealModule i, W)) :
    (actualIdealModuleAppKernelAddEquiv i V
      ((actualIdealModule i).presheaf.map (homOfLE h).op x) : Γ(X, V)) =
      actualSectionRestriction X h (actualIdealModuleAppKernelAddEquiv i W x) := by
  rw [actualIdealModuleAppKernelAddEquiv_coe,
    actualIdealModuleAppKernelAddEquiv_coe]
  exact ConcreteCategory.congr_hom
    ((actualIdealModuleToUnit i).val.naturality (homOfLE h).op) x

theorem actualNativeProductOpen_eq_iInf {X : Scheme.{u}}
    {α : Type v} (V : α → X.Opens) : (∏ᶜ V) = ⨅ a, V a :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (Preorder.isLimitIInf _)).to_eq

theorem actualNativeProductOpen_zero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (t : Fin 1 → ι) :
    (∏ᶜ fun k => U (t k)) = U (t 0) := by
  rw [actualNativeProductOpen_eq_iInf]
  apply le_antisymm
  · exact iInf_le _ 0
  · apply le_iInf; intro k; fin_cases k; rfl

theorem actualNativeProductOpen_one {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (t : Fin 2 → ι) :
    (∏ᶜ fun k => U (t k)) = U (t 0) ⊓ U (t 1) := by
  rw [actualNativeProductOpen_eq_iInf]
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · apply le_iInf; intro k; fin_cases k
    · exact inf_le_left
    · exact inf_le_right

theorem actualNativeProductOpen_two {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (t : Fin 3 → ι) :
    (∏ᶜ fun k => U (t k)) = (U (t 0) ⊓ U (t 1)) ⊓ U (t 2) := by
  rw [actualNativeProductOpen_eq_iInf]
  apply le_antisymm
  · exact le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
  · apply le_iInf; intro k; fin_cases k
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right

def actualModuleSectionTransport {X : Scheme.{u}} (M : X.Modules)
    {V W : X.Opens} (h : V = W) : Γ(M, V) ≃+ Γ(M, W) :=
  (M.presheaf.mapIso (eqToIso h.symm).op).addCommGroupIsoToAddEquiv

def actualModuleCechZeroEquiv {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (∀ t : Fin 1 → ι, Γ(M, ∏ᶜ fun k => U (t k))) ≃+ ∀ j, Γ(M, U j) where
  toFun a j := actualModuleSectionTransport M (actualNativeProductOpen_zero U ![j]) (a ![j])
  invFun a t := (actualModuleSectionTransport M (actualNativeProductOpen_zero U t)).symm
    (a (t 0))
  left_inv a := by
    funext t
    have ht : ![t 0] = t := by funext k; fin_cases k; rfl
    rw [← ht]
    exact AddEquiv.symm_apply_apply _ _
  right_inv a := by funext j; exact AddEquiv.apply_symm_apply _ _
  map_add' a b := by funext j; exact map_add _ _ _

def actualModuleCechOneEquiv {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (∀ t : Fin 2 → ι, Γ(M, ∏ᶜ fun k => U (t k))) ≃+
      ∀ j k, Γ(M, U j ⊓ U k) where
  toFun a j k := actualModuleSectionTransport M (actualNativeProductOpen_one U ![j,k])
    (a ![j,k])
  invFun a t := (actualModuleSectionTransport M (actualNativeProductOpen_one U t)).symm
    (a (t 0) (t 1))
  left_inv a := by
    funext t
    have ht : ![t 0,t 1] = t := by funext k; fin_cases k <;> rfl
    rw [← ht]
    exact AddEquiv.symm_apply_apply _ _
  right_inv a := by funext j k; exact AddEquiv.apply_symm_apply _ _
  map_add' a b := by funext j k; exact map_add _ _ _

def actualModuleCechTwoEquiv {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (∀ t : Fin 3 → ι, Γ(M, ∏ᶜ fun k => U (t k))) ≃+
      ∀ j k l, Γ(M, (U j ⊓ U k) ⊓ U l) where
  toFun a j k l := actualModuleSectionTransport M
    (actualNativeProductOpen_two U ![j,k,l]) (a ![j,k,l])
  invFun a t := (actualModuleSectionTransport M (actualNativeProductOpen_two U t)).symm
    (a (t 0) (t 1) (t 2))
  left_inv a := by
    funext t
    have ht : ![t 0,t 1,t 2] = t := by funext k; fin_cases k <;> rfl
    rw [← ht]
    exact AddEquiv.symm_apply_apply _ _
  right_inv a := by funext j k l; exact AddEquiv.apply_symm_apply _ _
  map_add' a b := by funext j k l; exact map_add _ _ _

def actualKernelZeroFamilyEquiv {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type u} (U : ι → X.Opens) :
    (∀ j, (i.app (U j)).hom.toAddMonoidHom.ker) ≃+
      (actualCechPullbackZero i U).ker where
  toFun a := ⟨fun j => (a j).1, by funext j; exact (a j).2⟩
  invFun a j := ⟨a.1 j, congrFun a.2 j⟩
  left_inv a := by rfl
  right_inv a := by rfl
  map_add' a b := by rfl

def actualKernelOneFamilyEquiv {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type u} (U : ι → X.Opens) :
    (∀ j k, (i.app (U j ⊓ U k)).hom.toAddMonoidHom.ker) ≃+
      (actualCechPullbackOne i U).ker where
  toFun a := ⟨fun j k => (a j k).1, by funext j k; exact (a j k).2⟩
  invFun a j k := ⟨a.1 j k, congrFun (congrFun a.2 j) k⟩
  left_inv a := by rfl
  right_inv a := by rfl
  map_add' a b := by rfl

abbrev actualNativeCechFactor {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (t : Fin (n + 1) → ι) :=
  (Scheme.Modules.baseModulePresheaf f M).obj (op (∏ᶜ fun k => U (t k)))

def actualNativeCechXIsoPi {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (Scheme.Modules.baseCechComplex f M U).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ t : Fin (n + 1) → ι, actualNativeCechFactor f M U n t) :=
  ModuleCat.piIsoPi _

def actualNativeCechZeroEquiv {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 0 ≃+
      (actualCechPullbackZero i U).ker :=
  (actualNativeCechXIsoPi f (actualIdealModule i) U 0).toLinearEquiv.toAddEquiv |>.trans
    (actualModuleCechZeroEquiv (actualIdealModule i) U) |>.trans
    (AddEquiv.piCongrRight (fun j => actualIdealModuleAppKernelAddEquiv i (U j))) |>.trans
    (actualKernelZeroFamilyEquiv i U)

def actualNativeCechOneEquiv {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 1 ≃+
      (actualCechPullbackOne i U).ker :=
  (actualNativeCechXIsoPi f (actualIdealModule i) U 1).toLinearEquiv.toAddEquiv |>.trans
    (actualModuleCechOneEquiv (actualIdealModule i) U) |>.trans
    (AddEquiv.piCongrRight (fun j => AddEquiv.piCongrRight
      (fun k => actualIdealModuleAppKernelAddEquiv i (U j ⊓ U k)))) |>.trans
    (actualKernelOneFamilyEquiv i U)

def actualNativeCechTwoEquiv {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 2 ≃+
      ∀ j k l, (i.app ((U j ⊓ U k) ⊓ U l)).hom.toAddMonoidHom.ker :=
  (actualNativeCechXIsoPi f (actualIdealModule i) U 2).toLinearEquiv.toAddEquiv |>.trans
    (actualModuleCechTwoEquiv (actualIdealModule i) U) |>.trans
    (AddEquiv.piCongrRight (fun j => AddEquiv.piCongrRight
      (fun k => AddEquiv.piCongrRight
        (fun l => actualIdealModuleAppKernelAddEquiv i ((U j ⊓ U k) ⊓ U l)))))

def actualNativeCechCoface {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    (Scheme.Modules.baseCechComplex f M U).X n ⟶
      (Scheme.Modules.baseCechComplex f M U).X (n + 1) :=
  ((FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ U).cech).obj (Scheme.Modules.baseModulePresheaf f M)).δ k

theorem actualNativeCech_d_comp_projection {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (t : Fin (n + 2) → ι) :
    (Scheme.Modules.baseCechComplex f M U).d n (n + 1) ≫
        Pi.π (fun j => actualNativeCechFactor f M U (n + 1) j) t =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (fun j => actualNativeCechFactor f M U n j)
            (t ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          (Scheme.Modules.baseModulePresheaf f M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ t).op) := by
  have hd : (Scheme.Modules.baseCechComplex f M U).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        actualNativeCechCoface f M U n k := by
    change ((FormalCoproduct.cochainComplexFunctor
      (FormalCoproduct.mk _ U).cech).obj
        (Scheme.Modules.baseModulePresheaf f M)).d n (n + 1) = _
    rw [FormalCoproduct.cochainComplexFunctor_obj_d]
    exact (CochainComplex.of_d _ _ n).trans rfl
  rw [hd, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Preadditive.zsmul_comp]
  congr 1
  change (Pi.lift fun j : Fin (n + 2) → ι =>
      Pi.π (fun l : Fin (n + 1) → ι => actualNativeCechFactor f M U n l)
          (j ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        (Scheme.Modules.baseModulePresheaf f M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ j).op) ≫ _ = _
  exact Pi.lift_comp_π _ t

theorem actualNativeCechZeroEquiv_coe {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 0) (j : ι) :
    (actualNativeCechZeroEquiv f i U x).1 j =
      (actualIdealModuleAppKernelAddEquiv i (U j)
        (actualModuleSectionTransport (actualIdealModule i)
          (actualNativeProductOpen_zero U ![j])
          ((Pi.π (fun t => actualNativeCechFactor f (actualIdealModule i) U 0 t)
            ![j]).hom x)) : Γ(X, U j)) := by
  change (actualIdealModuleAppKernelAddEquiv i (U j)
    (actualModuleSectionTransport (actualIdealModule i) (actualNativeProductOpen_zero U ![j])
      (((actualNativeCechXIsoPi f (actualIdealModule i) U 0).hom x) ![j])) : Γ(X, U j)) = _
  congr 2

theorem actualNativeCechOneEquiv_coe {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 1) (j k : ι) :
    (actualNativeCechOneEquiv f i U x).1 j k =
      (actualIdealModuleAppKernelAddEquiv i (U j ⊓ U k)
        (actualModuleSectionTransport (actualIdealModule i)
          (actualNativeProductOpen_one U ![j,k])
          ((Pi.π (fun t => actualNativeCechFactor f (actualIdealModule i) U 1 t)
            ![j,k]).hom x)) : Γ(X, U j ⊓ U k)) := by
  change (actualIdealModuleAppKernelAddEquiv i (U j ⊓ U k)
    (actualModuleSectionTransport (actualIdealModule i) (actualNativeProductOpen_one U ![j,k])
      (((actualNativeCechXIsoPi f (actualIdealModule i) U 1).hom x) ![j,k])) : Γ(X, U j ⊓ U k)) = _
  congr 2

theorem actualNativeCechZeroEquiv_coe_tuple {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 0)
    (t : Fin 1 → ι) :
    (actualNativeCechZeroEquiv f i U x).1 (t 0) =
      (actualIdealModuleAppKernelAddEquiv i (U (t 0))
        (actualModuleSectionTransport (actualIdealModule i)
          (actualNativeProductOpen_zero U t)
          ((Pi.π (fun a => actualNativeCechFactor f (actualIdealModule i) U 0 a)
            t).hom x)) : Γ(X, U (t 0))) := by
  have ht : ![t 0] = t := by funext a; fin_cases a; rfl
  rw [← ht]
  exact actualNativeCechZeroEquiv_coe f i U x (t 0)

theorem actualNativeCechOneEquiv_coe_tuple {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 1)
    (t : Fin 2 → ι) :
    (actualNativeCechOneEquiv f i U x).1 (t 0) (t 1) =
      (actualIdealModuleAppKernelAddEquiv i (U (t 0) ⊓ U (t 1))
        (actualModuleSectionTransport (actualIdealModule i)
          (actualNativeProductOpen_one U t)
          ((Pi.π (fun a => actualNativeCechFactor f (actualIdealModule i) U 1 a)
            t).hom x)) : Γ(X, U (t 0) ⊓ U (t 1))) := by
  have ht : ![t 0,t 1] = t := by funext a; fin_cases a <;> rfl
  rw [← ht]
  exact actualNativeCechOneEquiv_coe f i U x (t 0) (t 1)

theorem actualNativeCechTwoEquiv_coe {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 2) (j k l : ι) :
    (actualNativeCechTwoEquiv f i U x j k l : Γ(X, (U j ⊓ U k) ⊓ U l)) =
      (actualIdealModuleAppKernelAddEquiv i ((U j ⊓ U k) ⊓ U l)
        (actualModuleSectionTransport (actualIdealModule i)
          (actualNativeProductOpen_two U ![j,k,l])
          ((Pi.π (fun t => actualNativeCechFactor f (actualIdealModule i) U 2 t)
            ![j,k,l]).hom x)) : Γ(X, (U j ⊓ U k) ⊓ U l)) := by
  change (actualIdealModuleAppKernelAddEquiv i ((U j ⊓ U k) ⊓ U l)
    (actualModuleSectionTransport (actualIdealModule i) (actualNativeProductOpen_two U ![j,k,l])
      (((actualNativeCechXIsoPi f (actualIdealModule i) U 2).hom x) ![j,k,l])) :
        Γ(X, (U j ⊓ U k) ⊓ U l)) = _
  congr 2

theorem actualIdealModuleTransportRestriction {X Z : Scheme.{u}}
    (i : Z ⟶ X) {V V' W W' : X.Opens} (hV : V = V') (hW : W = W')
    (h : V ≤ W) (h' : V' ≤ W') (x : Γ(actualIdealModule i, W)) :
    (actualIdealModuleAppKernelAddEquiv i V'
      (actualModuleSectionTransport (actualIdealModule i) hV
        ((actualIdealModule i).presheaf.map (homOfLE h).op x)) : Γ(X, V')) =
      actualSectionRestriction X h'
        (actualIdealModuleAppKernelAddEquiv i W'
          (actualModuleSectionTransport (actualIdealModule i) hW x)) := by
  subst V'; subst W'
  simp only [actualModuleSectionTransport, eqToIso_refl, Iso.op_refl, Functor.mapIso_refl]
  exact actualIdealModuleAppKernelAddEquiv_naturality i h x

def actualIdealModuleTransportToRing {X Z : Scheme.{u}} (i : Z ⟶ X)
    {V W : X.Opens} (h : V = W) : Γ(actualIdealModule i, V) →+ Γ(X, W) :=
  ((i.app W).hom.toAddMonoidHom.ker.subtype).comp
    ((actualIdealModuleAppKernelAddEquiv i W).toAddMonoidHom.comp
      (actualModuleSectionTransport (actualIdealModule i) h).toAddMonoidHom)

theorem actualNativeCech_difference {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 0) :
    (actualNativeCechOneEquiv f i U
      ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).d 0 1 x)).1 =
        actualCechDifference X U (actualNativeCechZeroEquiv f i U x).1 := by
  funext j k
  let M := actualIdealModule i
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
  rw [actualNativeCechOneEquiv_coe]
  change _ = actualSectionRestriction X inf_le_right
      ((actualNativeCechZeroEquiv f i U x).1 k) -
    actualSectionRestriction X inf_le_left ((actualNativeCechZeroEquiv f i U x).1 j)
  rw [actualNativeCechZeroEquiv_coe, actualNativeCechZeroEquiv_coe]
  change actualIdealModuleTransportToRing i (actualNativeProductOpen_one U t) _ = _
  rw [hd, map_sub]
  change _ = actualSectionRestriction X inf_le_right _ -
    actualSectionRestriction X inf_le_left _
  congr 1
  · refine (actualIdealModuleTransportRestriction i
      (actualNativeProductOpen_one U t)
      (actualNativeProductOpen_zero U
        (t ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun))
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ t)) inf_le_right
      ((Pi.π (fun a => actualNativeCechFactor f M U 0 a)
        (t ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun)).hom x)).trans ?_
    exact congrArg (actualSectionRestriction X inf_le_right)
      ((actualNativeCechZeroEquiv_coe_tuple f i U x
        (t ∘ (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun)).symm.trans
          (actualNativeCechZeroEquiv_coe f i U x k))
  · refine (actualIdealModuleTransportRestriction i
      (actualNativeProductOpen_one U t)
      (actualNativeProductOpen_zero U
        (t ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun))
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ t)) inf_le_left
      ((Pi.π (fun a => actualNativeCechFactor f M U 0 a)
        (t ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).hom x)).trans ?_
    exact congrArg (actualSectionRestriction X inf_le_left)
      ((actualNativeCechZeroEquiv_coe_tuple f i U x
        (t ∘ (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).symm.trans
          (actualNativeCechZeroEquiv_coe f i U x j))

theorem actualNativeCech_boundary {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 1)
    (j k l : ι) :
    (actualNativeCechTwoEquiv f i U
      ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).d 1 2 x) j k l :
        Γ(X, (U j ⊓ U k) ⊓ U l)) =
      actualCechBoundary X U (actualNativeCechOneEquiv f i U x).1 j k l := by
  let M := actualIdealModule i
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
  rw [actualNativeCechTwoEquiv_coe]
  change _ = actualSectionRestriction X _ ((actualNativeCechOneEquiv f i U x).1 k l) -
    actualSectionRestriction X _ ((actualNativeCechOneEquiv f i U x).1 j l) +
    actualSectionRestriction X _ ((actualNativeCechOneEquiv f i U x).1 j k)
  rw [actualNativeCechOneEquiv_coe, actualNativeCechOneEquiv_coe,
    actualNativeCechOneEquiv_coe]
  change actualIdealModuleTransportToRing i (actualNativeProductOpen_two U t) _ = _
  rw [hd, map_add, map_sub]
  congr 1
  · congr 1
    · refine (actualIdealModuleTransportRestriction i
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
        ((actualNativeCechOneEquiv_coe_tuple f i U x
          (t ∘ (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun)).symm.trans
            (actualNativeCechOneEquiv_coe f i U x k l))
    · refine (actualIdealModuleTransportRestriction i
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
        ((actualNativeCechOneEquiv_coe_tuple f i U x
          (t ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFun)).symm.trans
            (actualNativeCechOneEquiv_coe f i U x j l))
  · refine (actualIdealModuleTransportRestriction i
      (actualNativeProductOpen_two U t)
      (actualNativeProductOpen_one U
        (t ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun))
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun).φ t)) inf_le_left
      ((Pi.π (fun a => actualNativeCechFactor f M U 1 a)
        (t ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun)).hom x)).trans ?_
    exact congrArg (actualSectionRestriction X inf_le_left)
      ((actualNativeCechOneEquiv_coe_tuple f i U x
        (t ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun)).symm.trans
          (actualNativeCechOneEquiv_coe f i U x j k))

theorem actualNativeCech_cycle_iff {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 1) :
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).d 1 2 x = 0 ↔
      actualCechBoundary X U (actualNativeCechOneEquiv f i U x).1 = 0 := by
  constructor
  · intro hx
    funext j k l
    rw [← actualNativeCech_boundary, hx]
    simp only [map_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
    rfl
  · intro hx
    apply (actualNativeCechTwoEquiv f i U).injective
    funext j k l
    apply Subtype.ext
    rw [actualNativeCech_boundary]
    simp only [map_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
    exact (congrFun (congrFun (congrFun hx j) k) l).trans (by rfl)

def actualNativeCechCycleEquiv {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).g.hom.ker ≃+
      actualClosedCechCocycles i U where
  toFun a := ⟨(actualNativeCechOneEquiv f i U a.1).1,
    (actualNativeCechOneEquiv f i U a.1).2,
    (actualNativeCech_cycle_iff f i U a.1).mp a.2⟩
  invFun a := ⟨(actualNativeCechOneEquiv f i U).symm ⟨a.1, a.2.1⟩,
    (actualNativeCech_cycle_iff f i U _).mpr (by
      have h := congrArg Subtype.val
        ((actualNativeCechOneEquiv f i U).apply_symm_apply ⟨a.1, a.2.1⟩)
      rw [h]
      exact a.2.2)⟩
  left_inv a := by
    apply Subtype.ext
    exact (actualNativeCechOneEquiv f i U).symm_apply_apply a.1
  right_inv a := by
    apply Subtype.ext
    change (actualNativeCechOneEquiv f i U
      ((actualNativeCechOneEquiv f i U).symm ⟨a.1, a.2.1⟩)).1 = a.1
    exact congrArg Subtype.val
      ((actualNativeCechOneEquiv f i U).apply_symm_apply ⟨a.1, a.2.1⟩)
  map_add' a b := by
    apply Subtype.ext
    change (actualNativeCechOneEquiv f i U (a.1 + b.1)).1 =
      ((actualNativeCechOneEquiv f i U a.1) + (actualNativeCechOneEquiv f i U b.1)).1
    exact congrArg Subtype.val (map_add (actualNativeCechOneEquiv f i U) a.1 b.1)

theorem actualNativeCechCycleEquiv_boundary {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 0) :
    actualNativeCechCycleEquiv f i U
      (((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).moduleCatToCycles x) =
        actualClosedCechBoundary i U (actualNativeCechZeroEquiv f i U x) := by
  apply Subtype.ext
  exact actualNativeCech_difference f i U x

theorem actualNativeCechCycleEquiv_range {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).moduleCatToCycles.range.toAddSubgroup).map
      (actualNativeCechCycleEquiv f i U).toAddMonoidHom = (actualClosedCechBoundary i U).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    exact ⟨actualNativeCechZeroEquiv f i U x,
      (actualNativeCechCycleEquiv_boundary f i U x).symm⟩
  · rintro ⟨x, rfl⟩
    let y := (actualNativeCechZeroEquiv f i U).symm x
    refine ⟨((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).moduleCatToCycles y,
      ⟨y, rfl⟩, ?_⟩
    exact (actualNativeCechCycleEquiv_boundary f i U y).trans
      (congrArg (actualClosedCechBoundary i U)
        ((actualNativeCechZeroEquiv f i U).apply_symm_apply x))

def actualNativeCechHOneExplicitIso {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).homology 1 ≅
      ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).homology :=
  ShortComplex.homologyMapIso
    ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).isoSc' 0 1 2
      (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1))

def actualNativeCechHOneAddEquiv {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).homology 1 ≃+
      actualClosedCechHOne i U :=
  (actualNativeCechHOneExplicitIso f i U).toLinearEquiv.toAddEquiv.trans
    ((((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.trans
    (QuotientAddGroup.congr _ _ (actualNativeCechCycleEquiv f i U)
      (actualNativeCechCycleEquiv_range f i U)))

theorem actualNativeCechOneEquiv_smul {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤))
    (x : (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).X 1) :
    (actualNativeCechOneEquiv f i U (r • x)).1 =
      actualCechScaleOne X U (f.appTop r) (actualNativeCechOneEquiv f i U x).1 := by
  funext j k
  rw [actualNativeCechOneEquiv_coe]
  change _ = actualSectionRestriction X le_top (f.appTop r) *
    (actualNativeCechOneEquiv f i U x).1 j k
  rw [actualNativeCechOneEquiv_coe, actualIdealModuleAppKernelAddEquiv_coe,
    actualIdealModuleAppKernelAddEquiv_coe]
  let V := U j ⊓ U k
  let t : Fin 2 → ι := ![j,k]
  let h := actualNativeProductOpen_one U t
  let φ := (Scheme.Modules.baseModulePresheaf f (actualIdealModule i)).map (eqToHom h.symm).op
  let p := Pi.π (fun a => actualNativeCechFactor f (actualIdealModule i) U 1 a) t
  let q : Γ(actualIdealModule i, V) →ₗ[Γ(X, V)] Γ(X, V) :=
    ((actualIdealModuleToUnit i).val.app (op V)).hom
  change q (φ.hom (p.hom (r • x))) =
    actualSectionRestriction X (U := V) le_top (f.appTop r) *
      q (φ.hom (p.hom x))
  rw [p.hom.map_smul, φ.hom.map_smul]
  exact q.map_smul
    (actualSectionRestriction X le_top (f.appTop r)) (φ.hom (p.hom x))

theorem actualNativeCechCycleEquiv_smul {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤))
    (a : ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2).g.hom.ker) :
    actualNativeCechCycleEquiv f i U (r • a) =
      actualClosedCechScaleCycle i U (f.appTop r) (actualNativeCechCycleEquiv f i U a) := by
  apply Subtype.ext
  exact actualNativeCechOneEquiv_smul f i U r a.1

def actualNativeCechHOneLinearEquiv {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    letI : Module Γ(S, ⊤) (actualClosedCechHOne i U) :=
      Module.compHom (actualClosedCechHOne i U) f.appTop.hom
    (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).homology 1 ≃ₗ[Γ(S, ⊤)]
      actualClosedCechHOne i U := by
  letI : Module Γ(S, ⊤) (actualClosedCechHOne i U) :=
    Module.compHom (actualClosedCechHOne i U) f.appTop.hom
  refine { actualNativeCechHOneAddEquiv f i U with map_smul' := ?_ }
  intro r x
  let K := (Scheme.Modules.baseCechComplex f (actualIdealModule i) U).sc' 0 1 2
  let q := QuotientAddGroup.congr _ _ (actualNativeCechCycleEquiv f i U)
    (actualNativeCechCycleEquiv_range f i U)
  have hq (z : K.moduleCatLeftHomologyData.H) : q (r • z) = r • q z := by
    induction z using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk' _ (actualNativeCechCycleEquiv f i U (r • a)) =
        QuotientAddGroup.mk' _ (actualClosedCechScaleCycle i U (f.appTop r)
          (actualNativeCechCycleEquiv f i U a))
      rw [actualNativeCechCycleEquiv_smul]
  change q (K.moduleCatHomologyIso.toLinearEquiv
      ((actualNativeCechHOneExplicitIso f i U).toLinearEquiv (r • x))) =
    r • q (K.moduleCatHomologyIso.toLinearEquiv
      ((actualNativeCechHOneExplicitIso f i U).toLinearEquiv x))
  simp only [map_smul]
  exact hq _

/-- Native sheaf-module Čech cohomology and the actual all-pairs kernel obstruction
are canonically equivalent as modules over the global functions on the base.
This comparison requires no assumed cohomology identification, affine geometry,
or finite-generation hypothesis. -/
theorem actual_closed_cech_native_comparison {X Z S : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    letI : Module Γ(S, ⊤) (actualClosedCechHOne i U) :=
      Module.compHom (actualClosedCechHOne i U) f.appTop.hom
    Nonempty ((Scheme.Modules.baseCechComplex f (actualIdealModule i) U).homology 1 ≃ₗ[Γ(S, ⊤)]
      actualClosedCechHOne i U) :=
  ⟨actualNativeCechHOneLinearEquiv f i U⟩

end
end Negativity
