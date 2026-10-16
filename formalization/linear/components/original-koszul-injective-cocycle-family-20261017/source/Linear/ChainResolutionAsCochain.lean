/-
Adapted from mathlib CategoryTheory/Abelian/Projective/Extend.lean.
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the mathlib LICENSE.
-/
module
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Extend an ACTUAL nonnegative chain complex to integer cochain degrees,
retaining its original term C_n in cochain degree -n. No projective-term
assumption is used. -/
def originalChainAsCochain (C : ChainComplex A ℕ) : CochainComplex A ℤ :=
  C.extend ComplexShape.embeddingDownNat

def originalChainAsCochainXIso (C : ChainComplex A ℕ) (p : ℤ) (n : ℕ)
    (h : -(n : ℤ) = p) : (originalChainAsCochain C).X p ≅ C.X n :=
  HomologicalComplex.extendXIso C ComplexShape.embeddingDownNat h

/-- Preserve the SAME original differential under the actual degree
conversion; this also fixes the convention for original Ext classes. -/
theorem originalChainAsCochain_d (C : ChainComplex A ℕ) (p₁ p₂ : ℤ)
    (n₁ n₂ : ℕ) (h₁ : -(n₁ : ℤ) = p₁) (h₂ : -(n₂ : ℤ) = p₂) :
    (originalChainAsCochain C).d p₁ p₂ =
      (originalChainAsCochainXIso C p₁ n₁ h₁).hom ≫ C.d n₁ n₂ ≫
        (originalChainAsCochainXIso C p₂ n₂ h₂).inv :=
  HomologicalComplex.extend_d_eq C ComplexShape.embeddingDownNat h₁ h₂

/-- Convert the ACTUAL original augmentation, rather than replacing its
source or target by a freely specified cochain model. -/
def originalChainAugmentationAsCochain (C : ChainComplex A ℕ) {E : A}
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) :
    originalChainAsCochain C ⟶ (CochainComplex.singleFunctor A 0).obj E :=
  (ComplexShape.embeddingDownNat.extendFunctor A).map alpha ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat E 0 0 (by simp)).hom

/-- The native extension functor preserves the actual augmentation's
quasi-isomorphism. Actual original applications must prove the latter. -/
theorem originalChainAugmentationAsCochain_quasiIso (C : ChainComplex A ℕ) {E : A}
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha] :
    QuasiIso (originalChainAugmentationAsCochain C alpha) := by
  change QuasiIso (HomologicalComplex.extendMap alpha ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat E 0 0 (by simp)).hom)
  infer_instance

end LinearStudy
