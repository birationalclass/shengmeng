/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module
public import Linear.ModuleOrderedBaseCechFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- Minimal generic extraction of the reviewed finite-coproduct argument in
CBirkbeck/AINTLIB ab1451487da02cd4483d0e2cdb2cc9e44bbbac17,
EllipticCurve/ProjectiveSpacePositiveTwistCoproductCech.lean, lines 35-88.
No foreign twist sheaf or projective-space comparison is imported. -/
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits
universe u

/-- A finite biproduct of actual module sheaves inherits exactness in a fixed
degree of the actual ordered base-linear Cech complex from its summands. -/
theorem orderedBaseCechComplex_coproduct_exactAt
    {X Y : Scheme.{u}} (π : X ⟶ Y) {ι I : Type u} [LinearOrder ι] [Fintype I]
    (U : ι → X.Opens) (M : I → X.Modules) (q : ℕ)
    (hM : ∀ i, (orderedBaseCechComplex π (M i) U).ExactAt q) :
    (orderedBaseCechComplex π (∐ M) U).ExactAt q := by
  classical
  letI : HasFiniteBiproducts.{u} X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts.{u} (ModuleCat.{u} Γ(Y, (⊤ : Y.Opens))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let F := orderedBaseCechComplexFunctor π U ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(Y, (⊤ : Y.Opens)))
      (ComplexShape.up ℕ) q
  letI : F.Additive := by dsimp only [F]; infer_instance
  letI : PreservesBiproduct M F := {
    preserves := fun hb => ⟨isBilimitOfTotal _ (by
      simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
      erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ }
  have hcomponent (i : I) : IsZero (F.obj (M i)) :=
    HomologicalComplex.ExactAt.isZero_homology (hM i)
  letI (i : I) : Subsingleton (F.obj (M i)) :=
    ModuleCat.subsingleton_of_isZero (hcomponent i)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  change IsZero (F.obj (∐ M))
  let e₀ : F.obj (∐ M) ≅ F.obj (biproduct M) :=
    F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (biproduct M) ≅ biproduct (F.obj ∘ M) := F.mapBiproduct M
  let e₂ := biproduct.isoProduct (F.obj ∘ M)
  let e₃ := ModuleCat.piIsoPi (F.obj ∘ M)
  apply (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃).isZero_iff.mpr
  exact @ModuleCat.isZero_of_subsingleton _ _ _
    ⟨fun x y => funext fun i =>
      @Subsingleton.elim (F.obj (M i))
        (ModuleCat.subsingleton_of_isZero (hcomponent i)) (x i) (y i)⟩

end AlgebraicGeometry.Scheme.Modules
