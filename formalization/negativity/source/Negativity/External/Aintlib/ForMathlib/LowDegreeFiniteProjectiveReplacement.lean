module

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Negativity.External.Aintlib.ForMathlib.BaseChangeKerCoker

@[expose] public section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false


/-!
# A finite-projective replacement for a two-term complex

This file proves the amplitude `[0, 1]` module-theoretic form of Mumford,
*Abelian Varieties*, Section 5, Lemma 1. Let `f : C0 → Z1` be a map of flat
modules over a Noetherian ring. If its kernel and cokernel are finite, then it
admits a two-term replacement `KZero → KOne` with `KZero` finite projective
and `KOne` finite free. Its degree-zero kernel and degree-one cokernel agree
with those of `f` after every algebra base change.

The Noetherian hypothesis belongs only to this algebraic construction. Geometric
applications over an arbitrary base must remove it by approximation before
exposing their final statements.
-/

open Function
open CategoryTheory
open TensorProduct
open scoped ChangeOfRings

universe u v w

namespace ModularCurves

variable {R : Type u} [CommRing R]
variable {P Q T : Type v} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
  [Module R P] [Module R Q] [Module R T]

/-- The usual algebra tensor product is the object produced by categorical extension of
scalars along the algebra map. -/
noncomputable def moduleCatExtendScalarsObjLinearEquiv
    (A : Type w) [CommRing A] [Algebra R A] (M : ModuleCat.{v} R) :
    (A ⊗[R] M) ≃ₗ[A]
      (ModuleCat.extendScalars.{u, w, v} (algebraMap R A)).obj M := by
  let Ares :=
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)
  letI : IsScalarTower R A Ares :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eA : A ≃ₗ[A] Ares := LinearEquiv.refl A A
  exact TensorProduct.AlgebraTensorModule.congr eA (LinearEquiv.refl R M)

/-- Extension of scalars along a ring equivalence is the inverse restriction-of-scalars
functor. -/
noncomputable def moduleCatExtendScalarsIsoRestrictScalarsOfRingEquiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    ModuleCat.extendScalars.{u, u, u} e.toRingHom ≅
      ModuleCat.restrictScalars.{u, u, u} e.symm.toRingHom :=
  (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

@[simp]
theorem moduleCatExtendScalarsObjLinearEquiv_tmul
    (A : Type w) [CommRing A] [Algebra R A] (M : ModuleCat.{v} R)
    (a : A) (m : M) :
    moduleCatExtendScalarsObjLinearEquiv A M (a ⊗ₜ[R] m) =
      a ⊗ₜ[R, algebraMap R A] m := by
  rfl

/-- The algebraic tensor-product comparison with categorical extension of scalars
intertwines base change of linear maps with the extension-of-scalars functor. -/
theorem moduleCatExtendScalarsObjLinearEquiv_baseChange
    (A : Type w) [CommRing A] [Algebra R A]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : A ⊗[R] M) :
    moduleCatExtendScalarsObjLinearEquiv A N
        (f.hom.baseChange A x) =
      (ModuleCat.extendScalars (algebraMap R A)).map f
        (moduleCatExtendScalarsObjLinearEquiv A M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [LinearMap.baseChange_tmul,
        moduleCatExtendScalarsObjLinearEquiv_tmul,
        moduleCatExtendScalarsObjLinearEquiv_tmul]
      exact (ModuleCat.ExtendScalars.map_tmul
        (f := algebraMap R A) f a m).symm
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      exact (((ModuleCat.extendScalars (algebraMap R A)).map f).hom.map_add _ _).symm

/-- The linear maps underlying a short complex of modules compose to zero. -/
theorem shortComplexModuleCatCompEqZero
    (S : ShortComplex (ModuleCat.{v} R)) :
    S.g.hom ∘ₗ S.f.hom = 0 := by
  apply LinearMap.ext
  intro x
  exact S.moduleCat_zero_apply x

/-- The short complex built from base-changed linear maps is canonically isomorphic to
categorical extension of scalars of the original short complex. -/
noncomputable def shortComplexModuleCatMkBaseChangeIso
    (S : ShortComplex (ModuleCat.{v} R))
    (A : Type v) [CommRing A] [Algebra R A] :
    ShortComplex.moduleCatMk
        (S.f.hom.baseChange A) (S.g.hom.baseChange A)
        (LinearMap.baseChange_comp_eq_zero S.f.hom S.g.hom
          (shortComplexModuleCatCompEqZero S) A) ≅
      S.map (ModuleCat.extendScalars.{u, v, v} (algebraMap R A)) :=
  ShortComplex.isoMk
    (moduleCatExtendScalarsObjLinearEquiv A S.X₁).toModuleIso
    (moduleCatExtendScalarsObjLinearEquiv A S.X₂).toModuleIso
    (moduleCatExtendScalarsObjLinearEquiv A S.X₃).toModuleIso
    (by
      letI : Module R
          ((S.map
            (ModuleCat.extendScalars.{u, v, v} (algebraMap R A))).X₂) :=
        Module.compHom _ (algebraMap R A)
      letI : IsScalarTower R A
          ((S.map
            (ModuleCat.extendScalars.{u, v, v} (algebraMap R A))).X₂) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      change a ⊗ₜ[R, algebraMap R A] S.f x =
        a ⊗ₜ[R, algebraMap R A] S.f x
      rfl)
    (by
      letI : Module R
          ((S.map
            (ModuleCat.extendScalars.{u, v, v} (algebraMap R A))).X₃) :=
        Module.compHom _ (algebraMap R A)
      letI : IsScalarTower R A
          ((S.map
            (ModuleCat.extendScalars.{u, v, v} (algebraMap R A))).X₃) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      change a ⊗ₜ[R, algebraMap R A] S.g x =
        a ⊗ₜ[R, algebraMap R A] S.g x
      rfl)

/-- The concrete cycle module of a short complex after algebraic base change is
canonically equivalent to the cycle module after categorical extension of scalars. -/
noncomputable def ShortComplex.baseChangeCyclesLinearEquiv
    (S : ShortComplex (ModuleCat.{v} R))
    (A : Type v) [CommRing A] [Algebra R A] :
    LinearMap.ker (S.g.hom.baseChange A) ≃ₗ[A]
      LinearMap.ker
        ((S.map (ModuleCat.extendScalars (algebraMap R A))).g.hom) := by
  let T := ShortComplex.moduleCatMk
    (S.f.hom.baseChange A) (S.g.hom.baseChange A)
    (LinearMap.baseChange_comp_eq_zero S.f.hom S.g.hom
      (shortComplexModuleCatCompEqZero S) A)
  exact (T.moduleCatCyclesIso.symm ≪≫
    ShortComplex.cyclesMapIso
      (shortComplexModuleCatMkBaseChangeIso S A) ≪≫
    (S.map (ModuleCat.extendScalars (algebraMap R A))).moduleCatCyclesIso).toLinearEquiv

/-- The kernel of the first differential after algebraic base change is canonically
equivalent to the first kernel after categorical extension of scalars. -/
noncomputable def HomologicalComplex.baseChangeKernelZeroLinearEquiv
    (K : CochainComplex (ModuleCat.{v} R) ℕ)
    (A : Type v) [CommRing A] [Algebra R A] :
    LinearMap.ker ((K.d 0 1).hom.baseChange A) ≃ₗ[A]
      LinearMap.ker
        ((((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℕ)).obj K).d 0 1).hom := by
  exact ShortComplex.baseChangeCyclesLinearEquiv (K.sc' 0 0 1) A

/-- The algebraic-to-categorical base-change equivalence on the degree-zero kernel has the
expected underlying extension-of-scalars element. -/
theorem HomologicalComplex.baseChangeKernelZeroLinearEquiv_coe
    (K : CochainComplex (ModuleCat.{v} R) ℕ)
    (A : Type v) [CommRing A] [Algebra R A]
    (x : LinearMap.ker ((K.d 0 1).hom.baseChange A)) :
    (HomologicalComplex.baseChangeKernelZeroLinearEquiv K A x).1 =
      moduleCatExtendScalarsObjLinearEquiv A (K.X 0) x.1 := by
  let S := K.sc' 0 0 1
  let T := ShortComplex.moduleCatMk
    (S.f.hom.baseChange A) (S.g.hom.baseChange A)
    (LinearMap.baseChange_comp_eq_zero S.f.hom S.g.hom
      (shortComplexModuleCatCompEqZero S) A)
  let e := shortComplexModuleCatMkBaseChangeIso S A
  change
    (((T.moduleCatCyclesIso.symm ≪≫
      ShortComplex.cyclesMapIso e ≪≫
      (S.map (ModuleCat.extendScalars (algebraMap R A))).moduleCatCyclesIso).hom x :
        LinearMap.ker
          ((S.map (ModuleCat.extendScalars (algebraMap R A))).g.hom))).1 = _
  have hcomp :
      ((T.moduleCatCyclesIso.symm ≪≫
          ShortComplex.cyclesMapIso e ≪≫
          (S.map (ModuleCat.extendScalars (algebraMap R A))).moduleCatCyclesIso).hom ≫
        (S.map (ModuleCat.extendScalars (algebraMap R A))).moduleCatLeftHomologyData.i) =
      T.moduleCatLeftHomologyData.i ≫ e.hom.τ₂ := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [(S.map (ModuleCat.extendScalars
      (algebraMap R A))).moduleCatCyclesIso_hom_i]
    change T.moduleCatCyclesIso.inv ≫
        ShortComplex.cyclesMap e.hom ≫
          (S.map (ModuleCat.extendScalars (algebraMap R A))).iCycles =
      T.moduleCatLeftHomologyData.i ≫ e.hom.τ₂
    rw [ShortComplex.cyclesMap_i]
    rw [T.moduleCatCyclesIso_inv_iCycles_assoc]
  exact ConcreteCategory.congr_hom hcomp x

/-- The inverse categorical-to-algebraic base-change equivalence on the degree-zero kernel
has the expected underlying tensor-product element. -/
theorem HomologicalComplex.baseChangeKernelZeroLinearEquiv_symm_coe
    (K : CochainComplex (ModuleCat.{v} R) ℕ)
    (A : Type v) [CommRing A] [Algebra R A]
    (x : LinearMap.ker
      (((((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex
        (.up ℕ)).obj K).d 0 1).hom)) :
    ((HomologicalComplex.baseChangeKernelZeroLinearEquiv K A).symm x).1 =
      (moduleCatExtendScalarsObjLinearEquiv A (K.X 0)).symm x.1 := by
  apply (moduleCatExtendScalarsObjLinearEquiv A (K.X 0)).injective
  rw [← HomologicalComplex.baseChangeKernelZeroLinearEquiv_coe]
  rw [(HomologicalComplex.baseChangeKernelZeroLinearEquiv K A).apply_symm_apply]
  symm
  exact (moduleCatExtendScalarsObjLinearEquiv A (K.X 0)).apply_symm_apply x.1


end ModularCurves
