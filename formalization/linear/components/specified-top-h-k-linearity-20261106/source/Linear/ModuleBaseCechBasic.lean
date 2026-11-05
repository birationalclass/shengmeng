/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Linear.ModuleFormalCoproductAdditive

/-!
# Base-linear Cech complexes of scheme modules

This file retains the module structure over the global functions on the base
in the native Cech complex of a scheme module.
-/

/- Minimal adaptation of CBirkbeck/AINTLIB, commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17
   projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechBasic.lean
   Upstream SHA-256 7a84970c70c62c377125dcd904cb3ec530c406658ee60fb393e6672e9c6f549c
   Actual base-linear section presheaf and Cech complex; omit unused open-immersion comparison proofs.
   Original4.1/4.2 and the uniform positive-twist bound remain open. -/

@[expose] public section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Inverse image commutes with the finite product open indexing a Cech cochain factor. -/
theorem Scheme.Hom.preimage_cechIntersection
    {X Y : Scheme.{u}} (g : Y ⟶ X) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    g ⁻¹ᵁ (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ∏ᶜ fun k : Fin (n + 1) => g ⁻¹ᵁ U (i k) := by
  rw [show (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ⨅ k, U (i k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  rw [show (∏ᶜ fun k : Fin (n + 1) => g ⁻¹ᵁ U (i k)) =
      ⨅ k, g ⁻¹ᵁ U (i k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  ext y
  rw [TopologicalSpace.Opens.coe_iInf]
  change g y ∈ (((⨅ k, U (i k)) : X.Opens) : Set X) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf]
  simp

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Sections of a scheme module, regarded functorially as modules over the
global functions on the base. -/
noncomputable def baseModulePresheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).obj M.1 ⋙
    ModuleCat.restrictScalars π.appTop.hom

@[simp]
theorem baseModulePresheaf_obj_coe {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (V : X.Opensᵒᵖ) :
    ((baseModulePresheaf π M).obj V : Type u) = M.presheaf.obj V :=
  rfl

@[simp]
theorem baseModulePresheaf_map_apply {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {V W : X.Opensᵒᵖ} (f : V ⟶ W)
    (x : M.presheaf.obj V) :
    ((baseModulePresheaf π M).map f).hom x = M.presheaf.map f x :=
  rfl

/-- The base-linear presheaf underlying a scheme module is a sheaf. -/
theorem baseModulePresheaf_isSheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (baseModulePresheaf π M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget (ModuleCat.{u} Γ(S, (⊤ : S.Opens))))]
  convert
    (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat.{u})).mp
      (Scheme.Modules.isSheaf M) using 1
  all_goals rfl

/-- A scheme module, regarded as a sheaf of modules over the global
functions on the base. -/
noncomputable def baseModuleSheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X)
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) :=
  ⟨baseModulePresheaf π M, baseModulePresheaf_isSheaf π M⟩

@[simp]
theorem baseModuleSheaf_obj_coe {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (V : X.Opensᵒᵖ) :
    ((baseModuleSheaf π M).obj.obj V : Type u) = M.presheaf.obj V :=
  rfl

@[simp]
theorem baseModuleSheaf_map_apply {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {V W : X.Opensᵒᵖ} (f : V ⟶ W)
    (x : M.presheaf.obj V) :
    ((baseModuleSheaf π M).obj.map f).hom x = M.presheaf.map f x :=
  rfl

/-- Sections over source opens, functorially regarded as modules over the base ring. -/
noncomputable def baseModulePresheafFunctor {X S : Scheme.{u}} (π : X ⟶ S) :
    X.Modules ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  toPresheafOfModules X ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop) ⋙
    (Functor.whiskeringRight X.Opensᵒᵖ _ _).obj
      (ModuleCat.restrictScalars π.appTop.hom)

@[simp]
theorem baseModulePresheafFunctor_obj {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    (baseModulePresheafFunctor π).obj M = baseModulePresheaf π M :=
  rfl

instance baseModulePresheafFunctor_preservesZeroMorphisms
    {X S : Scheme.{u}} (π : X ⟶ S) :
    (baseModulePresheafFunctor π).PreservesZeroMorphisms where
  map_zero M N := by
    ext U x
    rfl

instance baseModulePresheafFunctor_additive
    {X S : Scheme.{u}} (π : X ⟶ S) :
    (baseModulePresheafFunctor π).Additive where
  map_add := by
    intro M N f g
    ext U x
    rfl

/-- The Cech complex of a scheme module, retaining its module structure over
the global functions on the base. -/
noncomputable def baseCechComplex {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  (cechComplexFunctor U).obj (baseModulePresheaf π M)

/-- The base-linear Cech complex, functorially in the scheme module. -/
noncomputable def baseCechComplexFunctor {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  baseModulePresheafFunctor π ⋙ cechComplexFunctor U

@[simp]
theorem baseCechComplexFunctor_obj {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) (M : X.Modules) :
    (baseCechComplexFunctor π U).obj M = baseCechComplex π M U :=
  rfl

instance moduleCatCechComplexFunctor_preservesZeroMorphisms
    {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type u}
    (U : ι → X.Opens) :
    (cechComplexFunctor (A := ModuleCat.{u} R) U).PreservesZeroMorphisms where
  map_zero F G := by
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun _ ↦ 0) = 0
    refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Pi.map_π, comp_zero]
    exact zero_comp.symm

instance baseCechComplexFunctor_preservesZeroMorphisms
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} (U : ι → X.Opens) :
    (baseCechComplexFunctor π U).PreservesZeroMorphisms := by
  dsimp only [baseCechComplexFunctor]
  infer_instance

end

end AlgebraicGeometry.Scheme.Modules
