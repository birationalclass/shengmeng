/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

The base-linear short-exact-sequence proof is minimally adapted from
CBirkbeck/AINTLIB, commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17,
ForMathlib/SchemeModuleBaseCechExact.lean. The affine surjectivity and
underlying additive-sheaf exactness reuse already checked Linear code.
-/
module
public import Linear.ModuleBaseCechBasic
public import Linear.QuasicoherentAffineOpenSections
public import Linear.SchemeModuleAdditiveSheafColimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u

namespace LinearStudy

/-- The actual map on an arbitrary affine open is surjective for an
epimorphism between quasi-coherent module sheaves. The affine chart
and its image equality are constructed from the original affine open. -/
theorem quasicoherent_sections_surjective_on_isAffineOpen
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Function.Surjective (f.app U) := by
  let j : Spec Γ(X,U) ⟶ X := hU.isoSpec.inv ≫ U.ι
  have h := quasicoherent_sections_surjective_on_affineOpen Γ(X,U) j f
  have himage : j ''ᵁ ⊤ = U := by
    simp [j]
  rw [himage] at h
  exact h

end LinearStudy

namespace AlgebraicGeometry

/-- Finite nonempty intersections of actual affine opens are affine
on a separated scheme; these are exactly the actual Cech factor opens. -/
theorem IsAffineOpen.cechIntersection {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k : Fin (n + 1) => U (i k)) := by
  rw [show (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ⨅ k : Fin (n + 1), U (i k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  exact IsAffineOpen.iInf (fun k => hU (i k))

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- An actual short exact sequence of quasi-coherent scheme modules is
short exact on base-linear sections of any actual affine open. No
sectionwise epimorphism or kernel comparison certificate is an input. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.map_baseModulePresheafFunctor_eval_of_isAffineOpen
    {X S : Scheme.{u}} (π : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (T.map (baseModulePresheafFunctor π ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ
        (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))).ShortExact := by
  let A := T.map (baseModulePresheafFunctor π ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))
  let K := T.map (LinearStudy.schemeModuleToAdditiveSheaf X)
  have hK : K.ShortExact :=
    LinearStudy.schemeModuleShortExact_underlyingAdditiveSheaf T hT
  haveI : Mono T.f := hT.mono_f
  haveI : Epi T.g := hT.epi_g
  haveI : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (K.f.hom.app (op U)).hom
    haveI : Mono K.f := hK.mono_f
    haveI : Mono K.f.hom := by
      change Mono ((TopCat.Sheaf.forget AddCommGrpCat X).map K.f)
      infer_instance
    haveI : Mono (K.f.hom.app (op U)) := by infer_instance
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  haveI : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    exact LinearStudy.quasicoherent_sections_surjective_on_isAffineOpen U hU T.g
  refine ShortComplex.ShortExact.mk ?_
  change A.Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have hy' : K.g.hom.app (op U) y = 0 := hy
  obtain ⟨x, hx⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (U := U) hK.exact hK.mono_f y hy'
  exact ⟨x, hx⟩

end AlgebraicGeometry.Scheme.Modules
