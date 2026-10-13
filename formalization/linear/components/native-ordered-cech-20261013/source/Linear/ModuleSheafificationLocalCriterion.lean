/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Minimal adaptation of AINTLIB SheafOfModulesMonoidal.lean,
commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17, lines 70-89.
Only the module-sheafification criterion is used here.
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory
universe v v' u u'
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Actual module-sheafification inverts exactly the locally bijective
underlying presheaf maps. This is a generic site theorem, not a claim
that a particular projective tensor map already meets its hypotheses. -/
theorem moduleSheafification_isIso_iff_locallyBijective
    {M N : PresheafOfModules.{v} R₀} (f : M ⟶ N) :
    IsIso ((PresheafOfModules.sheafification.{v} α).map f) ↔
      Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R₀).map f) ∧
        Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R₀).map f) := by
  constructor
  · intro h
    have h1 : IsIso ((SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafification.{v} α).map f)) := inferInstance
    have h2 : IsIso ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf R₀).map f)) := h1
    have h3 : J.W ((PresheafOfModules.toPresheaf R₀).map f) := (J.W_iff _).mpr h2
    exact ⟨h3.isLocallyInjective, h3.isLocallySurjective⟩
  · rintro ⟨h1, h2⟩
    have h3 : J.W ((PresheafOfModules.toPresheaf R₀).map f) := J.W_of_isLocallyBijective _
    have h4 : IsIso ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf R₀).map f)) := (J.W_iff _).mp h3
    have h5 : IsIso ((SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafification.{v} α).map f)) := h4
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

end LinearStudy
