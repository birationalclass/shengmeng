module
public import Linear.ModuleOrderedBaseCechFunctor
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import all Linear.ModuleOrderedBaseCech
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X Y : Scheme.{u}} (π : X ⟶ Y) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The singleton ordered index corresponding to one member of the cover. -/
def orderedCechSingleton (i : ι) : OrderedCechIndex ι 0 :=
  ⟨fun _ => i, by
    intro a b hab
    exact False.elim ((ne_of_lt hab) (Fin.ext (by omega)))⟩

private def singletonOpenLift (i : ι) :
    U i ⟶ ∏ᶜ fun k : Fin 1 => U ((orderedCechSingleton i).1 k) :=
  Pi.lift fun _ => 𝟙 (U i)

/-- Global sections restrict to actual degree-zero ordered Cech cochains. -/
def orderedBaseCechAugmentation :
    (baseModulePresheaf π M).obj (op ⊤) ⟶ orderedBaseCechObject π M U 0 :=
  Pi.lift fun _ => (baseModulePresheaf π M).map (homOfLE le_top).op

@[reassoc]
theorem orderedBaseCechAugmentation_comp_π (i : OrderedCechIndex ι 0) :
    orderedBaseCechAugmentation π M U ≫
      Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1) i =
      (baseModulePresheaf π M).map (homOfLE le_top).op :=
  Pi.lift_comp_π _ i

/-- Restrictions of global sections are degree-zero cocycles. -/
theorem orderedBaseCechAugmentation_comp_d :
    orderedBaseCechAugmentation π M U ≫
      orderedBaseCechDifferential π M U 0 = 0 := by
  apply Pi.hom_ext
  intro i
  change (orderedBaseCechAugmentation π M U ≫ orderedBaseCechDifferential π M U 0) ≫
      Pi.π (fun j : OrderedCechIndex ι 1 => baseCechFactor π M U 1 j.1) i =
    (0 : (baseModulePresheaf π M).obj (op ⊤) ⟶ orderedBaseCechObject π M U 1) ≫
      Pi.π (fun j : OrderedCechIndex ι 1 => baseCechFactor π M U 1 j.1) i
  erw [Category.assoc, orderedBaseCechDifferential_zero_comp_π_sub,
    Preadditive.comp_sub, orderedBaseCechAugmentation_comp_π_assoc,
    orderedBaseCechAugmentation_comp_π_assoc,
    ← (baseModulePresheaf π M).map_comp, ← (baseModulePresheaf π M).map_comp]
  conv_rhs => rw [zero_comp]
  apply sub_eq_zero.mpr
  congr 1

private theorem orderedCech_element_ext (n : ℕ)
    (a b : orderedBaseCechObject π M U n)
    (h : ∀ i : OrderedCechIndex ι n,
      (Pi.π (fun j => baseCechFactor π M U n j.1) i) a =
      (Pi.π (fun j => baseCechFactor π M U n j.1) i) b) : a = b := by
  apply (ModuleCat.mono_iff_injective (orderedBaseCechObjectIsoPi π M U n).hom).mp
    (inferInstance : Mono (orderedBaseCechObjectIsoPi π M U n).hom)
  funext i
  change ((orderedBaseCechObjectIsoPi π M U n).hom ≫
    ModuleCat.ofHom (LinearMap.proj i)) a =
      ((orderedBaseCechObjectIsoPi π M U n).hom ≫
        ModuleCat.ofHom (LinearMap.proj i)) b
  erw [ModuleCat.piIsoPi_hom_ker_subtype]
  convert h i using 1
  all_goals rfl

private def orderedCechPair (i j : ι) (hij : i < j) : OrderedCechIndex ι 1 :=
  ⟨![i,j], by
    erw [Fin.strictMono_iff_lt_succ]
    intro k
    fin_cases k
    exact hij⟩

private theorem orderedCechPair_delete_zero (i j : ι) (hij : i < j) :
    (orderedCechPair i j hij).delete 0 = orderedCechSingleton j := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

private theorem orderedCechPair_delete_one (i j : ι) (hij : i < j) :
    (orderedCechPair i j hij).delete 1 = orderedCechSingleton i := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

private def pairOpenLift (i j : ι) (hij : i < j) :
    U i ⊓ U j ⟶ ∏ᶜ fun k : Fin 2 => U ((orderedCechPair i j hij).1 k) :=
  Pi.lift fun k => homOfLE (by
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right)

private def orderedCechLocalSection
    (c : orderedBaseCechObject π M U 0) (i : ι) : Γ(M,U i) :=
  M.presheaf.map (singletonOpenLift U i).op
    ((Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1)
      (orderedCechSingleton i)) c)

private theorem orderedCechRestriction_congr
    (a b : OrderedCechIndex ι 0) (hab : a = b) (V : X.Opens)
    (f : V ⟶ ∏ᶜ fun k : Fin 1 => U (a.1 k))
    (g : V ⟶ ∏ᶜ fun k : Fin 1 => U (b.1 k)) :
    Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1) a ≫
        (baseModulePresheaf π M).map f.op =
      Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1) b ≫
        (baseModulePresheaf π M).map g.op := by
  subst b
  rw [show f = g from Subsingleton.elim _ _]

private theorem orderedCechLocalSection_compatible_lt
    (c : orderedBaseCechObject π M U 0)
    (hc : orderedBaseCechDifferential π M U 0 c = 0)
    (i j : ι) (hij : i < j) :
    M.presheaf.map (Opens.infLELeft (U i) (U j)).op
      (orderedCechLocalSection π M U c i) =
    M.presheaf.map (Opens.infLERight (U i) (U j)).op
      (orderedCechLocalSection π M U c j) := by
  let p := orderedCechPair i j hij
  let F := baseModulePresheaf π M
  let proj := Pi.π (fun l : OrderedCechIndex ι 1 => baseCechFactor π M U 1 l.1) p
  have hz : ((orderedBaseCechCoface π M U 0 0 ≫ proj) -
      (orderedBaseCechCoface π M U 0 1 ≫ proj)) c = 0 := by
    have hd : orderedBaseCechDifferential π M U 0 =
      orderedBaseCechCoface π M U 0 0 - orderedBaseCechCoface π M U 0 1 := by
      simp [orderedBaseCechDifferential, Fin.sum_univ_two, sub_eq_add_neg]
    erw [← Preadditive.sub_comp, ← hd]
    simpa only [ConcreteCategory.comp_apply, hc, map_zero]
  have he := sub_eq_zero.mp hz
  have hl : orderedBaseCechCoface π M U 0 1 ≫ proj ≫
      F.map (pairOpenLift U i j hij).op =
    Pi.π (fun l : OrderedCechIndex ι 0 => baseCechFactor π M U 0 l.1)
      (orderedCechSingleton i) ≫ F.map (singletonOpenLift U i).op ≫
        F.map (Opens.infLELeft (U i) (U j)).op := by
    erw [← Category.assoc, orderedBaseCechCoface_comp_π,
      Category.assoc, ← F.map_comp]
    erw [← F.map_comp]
    exact orderedCechRestriction_congr π M U _ _
      (orderedCechPair_delete_one i j hij) _ _ _
  have hr : orderedBaseCechCoface π M U 0 0 ≫ proj ≫
      F.map (pairOpenLift U i j hij).op =
    Pi.π (fun l : OrderedCechIndex ι 0 => baseCechFactor π M U 0 l.1)
      (orderedCechSingleton j) ≫ F.map (singletonOpenLift U j).op ≫
        F.map (Opens.infLERight (U i) (U j)).op := by
    erw [← Category.assoc, orderedBaseCechCoface_comp_π,
      Category.assoc, ← F.map_comp]
    erw [← F.map_comp]
    exact orderedCechRestriction_congr π M U _ _
      (orderedCechPair_delete_zero i j hij) _ _ _
  have h := congrArg (fun z => F.map (pairOpenLift U i j hij).op z) he.symm
  change ((orderedBaseCechCoface π M U 0 1 ≫ proj) ≫
      F.map (pairOpenLift U i j hij).op) c =
    ((orderedBaseCechCoface π M U 0 0 ≫ proj) ≫
      F.map (pairOpenLift U i j hij).op) c at h
  erw [Category.assoc, hl, Category.assoc, hr] at h
  exact h

private theorem orderedCechLocalSection_compatible
    (c : orderedBaseCechObject π M U 0)
    (hc : orderedBaseCechDifferential π M U 0 c = 0) :
    TopCat.Presheaf.IsCompatible M.presheaf U (orderedCechLocalSection π M U c) := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact orderedCechLocalSection_compatible_lt π M U c hc i j hij
  · rfl
  · have h := orderedCechLocalSection_compatible_lt π M U c hc j i hji
    have ht := congrArg (fun z => M.presheaf.map (eqToHom (inf_comm (U i) (U j))).op z) h.symm
    have hleft : (Opens.infLERight (U j) (U i)).op ≫
        (eqToHom (inf_comm (U i) (U j))).op = (Opens.infLELeft (U i) (U j)).op :=
      Subsingleton.elim _ _
    have hright : (Opens.infLELeft (U j) (U i)).op ≫
        (eqToHom (inf_comm (U i) (U j))).op = (Opens.infLERight (U i) (U j)).op :=
      Subsingleton.elim _ _
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hleft, hright] using ht

private theorem orderedCechLocalSection_augmentation (s : Γ(M,⊤)) (i : ι) :
    orderedCechLocalSection π M U (orderedBaseCechAugmentation π M U s) i =
      M.presheaf.map (homOfLE le_top).op s := by
  have h : orderedBaseCechAugmentation π M U ≫
      Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1)
        (orderedCechSingleton i) ≫
      (baseModulePresheaf π M).map (singletonOpenLift U i).op =
        (baseModulePresheaf π M).map (homOfLE le_top).op := by
    erw [orderedBaseCechAugmentation_comp_π_assoc, ← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom h s

/-- Every actual degree-zero cocycle glues to a global section on a cover. -/
theorem orderedBaseCechAugmentation_surjective_cycles
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (c : orderedBaseCechObject π M U 0)
    (hc : orderedBaseCechDifferential π M U 0 c = 0) :
    ∃ s : Γ(M,⊤), orderedBaseCechAugmentation π M U s = c := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf,M.isSheaf⟩
  obtain ⟨s,hs,-⟩ := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top)
    hcover (orderedCechLocalSection π M U c)
      (orderedCechLocalSection_compatible π M U c hc)
  refine ⟨s, orderedCech_element_ext π M U 0 _ _ ?_⟩
  intro i
  have hi : i = orderedCechSingleton (i.1 0) := by
    apply Subtype.ext
    funext k
    exact congrArg i.1 (Fin.ext (by omega))
  erw [hi]
  have h := congrArg (fun z => M.presheaf.map
    (Pi.π (fun k : Fin 1 => U ((orderedCechSingleton (i.1 0)).1 k)) 0).op z) (hs (i.1 0))
  let j := i.1 0
  let p := Pi.π (fun k : Fin 1 => U ((orderedCechSingleton j).1 k)) 0
  have hid : M.presheaf.map (singletonOpenLift U j).op ≫ M.presheaf.map p.op = 𝟙 _ := by
    erw [← Functor.map_comp]
    erw [show (singletonOpenLift U j).op ≫ p.op = 𝟙 _ from Subsingleton.elim _ _]
    exact M.presheaf.map_id _
  have htop : M.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op ≫
      M.presheaf.map p.op = M.presheaf.map (homOfLE le_top).op := by
    erw [← Functor.map_comp]
    congr 1
  change M.presheaf.map p.op (M.presheaf.map (homOfLE le_top).op s) =
      M.presheaf.map p.op (M.presheaf.map (singletonOpenLift U j).op
        ((Pi.π (fun l : OrderedCechIndex ι 0 => baseCechFactor π M U 0 l.1)
          (orderedCechSingleton j)) c)) at h
  change (M.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op ≫ M.presheaf.map p.op) s =
    (M.presheaf.map (singletonOpenLift U j).op ≫ M.presheaf.map p.op)
      ((Pi.π (fun l : OrderedCechIndex ι 0 => baseCechFactor π M U 0 l.1)
        (orderedCechSingleton j)) c) at h
  erw [htop, hid, ConcreteCategory.id_apply] at h
  exact (ConcreteCategory.congr_hom
    (orderedBaseCechAugmentation_comp_π π M U (orderedCechSingleton j)) s).trans h

/-- Global sections are determined by their actual degree-zero restrictions. -/
theorem orderedBaseCechAugmentation_injective (hcover : (⊤ : X.Opens) ≤ iSup U) :
    Function.Injective (orderedBaseCechAugmentation π M U) := by
  intro s t h
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf,M.isSheaf⟩
  apply F.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hcover
  intro i
  have hi := congrArg (fun c => orderedCechLocalSection π M U c i) h
  simpa only [orderedCechLocalSection_augmentation] using hi
end AlgebraicGeometry.Scheme.Modules
